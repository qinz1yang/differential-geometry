import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereZero
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
# The even height `p₀²` on `ℝP³` and its regular sublevel `{p₀² ≤ 16/25}`

Lane S-FIX-REG2 (suffix `_FXR`), G4 part 1 (D78-5 (1), `SelectedSmoothCore74.puncturedRP3`).
`ℝP³ = projectiveThreeSpaceLift.{0}` is the quotient of `S³` (the tree's `sphereW`) by the
antipodal map. The square of the height `p₀ = ⟪p, e₀⟫` is even, so it descends to `ℝP³`
(`rp3Height2_FXR`); `rp3Defining_FXR = p₀² − 16/25` is smooth with regular zero level, and the
sublevel `{p₀² ≤ 16/25}` is the complement of the open ball `{p₀² > 16/25}` around `[e₀]`.

* `rp3Cover_FXR`: the covering map `S³ → ℝP³` (a local diffeomorphism, onto);
* `rp3Height2_FXR_cover`: `p₀²` of the image is `sphereHeight²`;
* `contMDiff_rp3Defining_FXR`, `rp3Defining_regular_FXR`: smooth, regular on the zero level.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace GC.GraphManifold.Assembly

local instance sphereFourDim_FXR : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

/-- The covering map `S³ → ℝP³` (on the universe-lifted carriers). -/
def rp3Cover_FXR (x : sphereW.Carrier) : projectiveThreeSpaceLift.{0}.Carrier :=
  ULift.up (SphericalSpaceFormGroup.antipodal.projection x.down)

theorem rp3Cover_surjective_FXR : Surjective rp3Cover_FXR := by
  intro y
  obtain ⟨x, hx⟩ := SphericalSpaceFormGroup.antipodal.projection_surjective y.down
  exact ⟨ULift.up x, by cases y; exact congrArg ULift.up hx⟩

theorem isLocalDiffeomorph_rp3Cover_FXR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ rp3Cover_FXR := by
  have h1 := standardThreeSphereLiftDiffeomorph.{0}.symm.isLocalDiffeomorph
  have h2 := SphericalSpaceFormGroup.antipodal.projection_isLocalDiffeomorph
  have h3 := (ClosedOrientedManifold.uliftDiffeomorph.{0, 0}
    SphericalSpaceFormGroup.antipodal.manifold.toClosedOrientedManifold).isLocalDiffeomorph
  intro x
  exact ((h1 x).comp (K := 𝓡 3) (P := SphericalSpaceFormGroup.antipodal.Orbit) (h2 _)).comp
    (K := 𝓡 3) (P := projectiveThreeSpaceLift.{0}.Carrier) (h3 _)

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- Points of the unit sphere with the same antipodal image differ by a sign. -/
theorem antipodal_orbit_cases_FXR (x y : sphere (0 : E4) 1)
    (h : SphericalSpaceFormGroup.antipodal.projection x =
      SphericalSpaceFormGroup.antipodal.projection y) :
    (y : E4) = x ∨ (y : E4) = -x := by
  obtain ⟨γ, hγ⟩ := (SphericalSpaceFormGroup.antipodal.projection_eq_iff x y).1 h
  have hv := congrArg (fun z : sphere (0 : E4) 1 => (z : E4)) hγ
  simp only [Geometry.sphereDiffeo_coe] at hv
  rcases γ.2 with h1 | h1
  · left
    rw [← hv, h1]
    rfl
  · right
    rw [← hv]
    have h2 : γ.val = LinearIsometryEquiv.neg ℝ := h1
    rw [h2]
    rfl

/-- The square of the height `⟪p, e₀⟫` on the antipodal quotient of the unit sphere. -/
def rp3Height2Orbit_FXR : SphericalSpaceFormGroup.antipodal.Orbit → ℝ :=
  Quotient.lift (fun p : sphere (0 : E4) 1 => sphereHeight₀ p ^ 2) (fun a b hab => by
    rcases antipodal_orbit_cases_FXR a b (Quotient.sound hab) with h | h
    · simp only [sphereHeight₀, h]
    · simp only [sphereHeight₀, h, inner_neg_left, neg_sq])

/-- **The even height** `p₀²` on `ℝP³`. -/
def rp3Height2_FXR (y : projectiveThreeSpaceLift.{0}.Carrier) : ℝ :=
  rp3Height2Orbit_FXR y.down

theorem rp3Height2_cover_FXR (x : sphereW.Carrier) :
    rp3Height2_FXR (rp3Cover_FXR x) = sphereHeight x ^ 2 :=
  rfl

theorem contMDiff_rp3Height2_FXR : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ rp3Height2_FXR :=
  isLocalDiffeomorph_rp3Cover_FXR.contMDiff_of_comp_of_surjective rp3Cover_surjective_FXR
    (by
      have h : rp3Height2_FXR ∘ rp3Cover_FXR = fun x => sphereHeight x ^ 2 :=
        funext rp3Height2_cover_FXR
      rw [h]
      exact contMDiff_sphereHeight.pow 2)

/-- **The defining function** `p₀² − 16/25` of the complement of the ball `{p₀² > 16/25}`. -/
def rp3Defining_FXR (y : projectiveThreeSpaceLift.{0}.Carrier) : ℝ :=
  rp3Height2_FXR y - 16 / 25

theorem contMDiff_rp3Defining_FXR : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ rp3Defining_FXR :=
  contMDiff_rp3Height2_FXR.sub contMDiff_const

theorem mfderiv_rp3Defining_cover_FXR (x : sphereW.Carrier) (hx : |sphereHeight x| < 1)
    (h0 : sphereHeight x ≠ 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (rp3Defining_FXR ∘ rp3Cover_FXR) x ≠ 0 := by
  have hS := (contMDiff_sphereHeight x).mdifferentiableAt (by simp) |>.hasMFDerivAt
  have hne := mfderiv_sphereHeight_ne_zero hx
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t ^ 2 - 16 / 25) (sphereHeight x)
      ((2 * sphereHeight x) • ContinuousLinearMap.id ℝ ℝ) := by
    have h := ((hasDerivAt_pow 2 (sphereHeight x)).sub_const (16 / 25 : ℝ)).hasFDerivAt
    exact (h.congr_fderiv (by ext; simp)).hasMFDerivAt
  have hd := (hg.comp x hS).mfderiv
  have hfun : rp3Defining_FXR ∘ rp3Cover_FXR = (fun t : ℝ => t ^ 2 - 16 / 25) ∘ sphereHeight :=
    rfl
  rw [hfun, hd]
  intro h
  apply hne
  ext v
  have h2 : (2 * sphereHeight x) • mfderiv sphereW.model 𝓘(ℝ, ℝ) sphereHeight x v = 0 :=
    congrArg (fun L : TangentSpace sphereW.model x →L[ℝ] ℝ => L v) h
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero two_ne_zero h0)
  · exact h3

/-- Regularity of the zero level of `p₀² − 16/25` on `ℝP³`. -/
theorem rp3Defining_regular_FXR (y : projectiveThreeSpaceLift.{0}.Carrier)
    (hy : rp3Defining_FXR y = 0) : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) rp3Defining_FXR y ≠ 0 := by
  obtain ⟨x, rfl⟩ := rp3Cover_surjective_FXR y
  have hsq : sphereHeight x ^ 2 = 16 / 25 := by
    have h : sphereHeight x ^ 2 - 16 / 25 = 0 := hy
    linarith
  have habs : |sphereHeight x| = 4 / 5 := by
    have h1 : |sphereHeight x| ^ 2 = (4 / 5) ^ 2 := by rw [sq_abs, hsq]; norm_num
    exact (pow_left_inj₀ (abs_nonneg _) (by norm_num) two_ne_zero).1 h1
  have h0 : sphereHeight x ≠ 0 := by
    intro h
    rw [h] at habs
    norm_num at habs
  exact GC.Seifert.mfderiv_ne_zero_of_comp (J := 𝓡 3) (s := rp3Cover_FXR) (y := x)
    (contMDiff_rp3Defining_FXR.mdifferentiableAt (by simp))
    (isLocalDiffeomorph_rp3Cover_FXR.contMDiff.mdifferentiableAt (by simp))
    (mfderiv_rp3Defining_cover_FXR x (by rw [habs]; norm_num) h0)

/-! ## The punctured projective space as a regular sublevel -/

/-- **`ℝP³` minus the open ball `{p₀² > 16/25}`**: the sublevel `{p₀² ≤ 16/25}`. -/
def rp3Set_FXR : Set projectiveThreeSpaceLift.{0}.Carrier := {y | rp3Defining_FXR y ≤ 0}

/-- The smooth boundary atlas of the regular sublevel `rp3Set_FXR`. -/
def rp3Atlas_FXR : SmoothBoundaryAtlas (𝓡 3) 3 rp3Set_FXR :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) (by simp) contMDiff_rp3Defining_FXR 0
    rp3Defining_regular_FXR

instance rp3Set_charted_FXR : ChartedSpace (EuclideanHalfSpace 3) rp3Set_FXR :=
  rp3Atlas_FXR.toChartedSpace

instance rp3Set_manifold_FXR : IsManifold (𝓡∂ 3) ∞ rp3Set_FXR := rp3Atlas_FXR.isManifold

theorem rp3Set_isBoundaryPoint_iff_FXR {x : rp3Set_FXR} :
    (𝓡∂ 3).IsBoundaryPoint x ↔ rp3Defining_FXR x.val = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2) (by simp)
    contMDiff_rp3Defining_FXR 0 rp3Defining_regular_FXR x

theorem isClosed_rp3Set_FXR : IsClosed rp3Set_FXR :=
  isClosed_le contMDiff_rp3Defining_FXR.continuous continuous_const

instance rp3Set_compact_FXR : CompactSpace rp3Set_FXR :=
  isCompact_iff_compactSpace.mp isClosed_rp3Set_FXR.isCompact

instance rp3Y_secondCountable_FXR :
    SecondCountableTopology projectiveThreeSpaceLift.{0}.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3))
    projectiveThreeSpaceLift.{0}.Carrier

/-! ### Connectedness: the sublevel is the image of a closed stereographic annulus -/

/-- The band `{|q₀| ≤ 4/5}` of `S³`: the preimage of `rp3Set_FXR`. -/
def rp3Band_FXR : Set sphereW.Carrier := {x | |sphereHeight x| ≤ 4 / 5}

theorem rp3Set_eq_image_FXR : rp3Set_FXR = rp3Cover_FXR '' rp3Band_FXR := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := rp3Cover_surjective_FXR y
    refine ⟨x, ?_, rfl⟩
    have h : sphereHeight x ^ 2 - 16 / 25 ≤ 0 := hy
    change |sphereHeight x| ≤ 4 / 5
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)]
    exact sq_le_sq.1 (by linarith)
  · rintro ⟨x, hx, rfl⟩
    change sphereHeight x ^ 2 - 16 / 25 ≤ 0
    have h : |sphereHeight x| ≤ 4 / 5 := hx
    have h2 := sq_le_sq.2 (show |sphereHeight x| ≤ |(4 / 5 : ℝ)| by
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)])
    linarith

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The closed annulus `2/3 ≤ ‖y‖ ≤ 6` of `ℝ³` (stereographic image of the band). -/
def rp3Annulus_FXR : Set E3 := {y | 2 / 3 ≤ ‖y‖ ∧ ‖y‖ ≤ 6}

theorem isConnected_rp3Annulus_FXR : IsConnected rp3Annulus_FXR := by
  have hS : IsConnected (sphere (0 : E3) 1) :=
    isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one
  have hI : IsConnected (Icc (2 / 3 : ℝ) 6) := isConnected_Icc (by norm_num)
  have himg : rp3Annulus_FXR =
      (fun p : E3 × ℝ => p.2 • p.1) '' (sphere (0 : E3) 1 ×ˢ Icc (2 / 3 : ℝ) 6) := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      have hy : ‖y‖ ≠ 0 := by
        intro h
        rw [h] at h1
        norm_num at h1
      refine ⟨(‖y‖⁻¹ • y, ‖y‖), ⟨?_, h1, h2⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy]
      · change ‖y‖ • (‖y‖⁻¹ • y) = y
        rw [smul_inv_smul₀ hy]
    · rintro ⟨⟨u, r⟩, ⟨hu, hr1, hr2⟩, rfl⟩
      have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
      have hr0 : 0 ≤ r := by linarith
      change 2 / 3 ≤ ‖r • u‖ ∧ ‖r • u‖ ≤ 6
      rw [norm_smul, hu1, Real.norm_eq_abs, abs_of_nonneg hr0, mul_one]
      exact ⟨hr1, hr2⟩
  rw [himg]
  exact (hS.prod hI).image _ (by fun_prop : Continuous fun p : E3 × ℝ => p.2 • p.1).continuousOn

theorem abs_stereo_le_iff_FXR {r : ℝ} (hr : 0 ≤ r) :
    |(r ^ 2 - 4) / (r ^ 2 + 4)| ≤ 4 / 5 ↔ 2 / 3 ≤ r ∧ r ≤ 6 := by
  have hpos : 0 < r ^ 2 + 4 := by positivity
  rw [abs_le, div_le_iff₀ hpos, le_div_iff₀ hpos]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

theorem rp3Band_eq_image_FXR : rp3Band_FXR = cycleBallAmbient false '' rp3Annulus_FXR := by
  ext x
  constructor
  · intro hx
    have hx' : |sphereHeight x| ≤ 4 / 5 := hx
    have hne : spherePoint x ≠ cycleBallPole := by
      intro h
      rw [sphereHeight_eq_one_iff.2 h] at hx'
      norm_num at hx'
    obtain ⟨y, rfl⟩ := exists_ambient_false hne
    refine ⟨y, ?_, rfl⟩
    rw [sphereHeight_ambient_false] at hx'
    exact (abs_stereo_le_iff_FXR (norm_nonneg y)).1 hx'
  · rintro ⟨y, hy, rfl⟩
    change |sphereHeight (cycleBallAmbient false y)| ≤ 4 / 5
    rw [sphereHeight_ambient_false]
    exact (abs_stereo_le_iff_FXR (norm_nonneg y)).2 hy

theorem isConnected_rp3Set_FXR : IsConnected rp3Set_FXR := by
  have hc : Continuous (cycleBallAmbient false) := by
    have h := (cycleBallAmbient false).contMDiffOn_toFun.continuousOn
    rwa [cycleBallAmbient_source, continuousOn_univ] at h
  rw [rp3Set_eq_image_FXR, rp3Band_eq_image_FXR]
  exact (isConnected_rp3Annulus_FXR.image _ hc.continuousOn).image _
    isLocalDiffeomorph_rp3Cover_FXR.contMDiff.continuous.continuousOn

instance rp3Set_connected_FXR : ConnectedSpace rp3Set_FXR :=
  isConnected_iff_connectedSpace.mp isConnected_rp3Set_FXR

/-! ### The solid parametrization -/

/-- **The punctured `ℝP³` as a solid parametrization** of `rp3Set_FXR`. -/
def rp3Solid_FXR : SolidParam74.{0, 0} rp3Set_FXR where
  Piece := rp3Set_FXR
  param := Subtype.val
  embedding := rp3Atlas_FXR.isSmoothEmbedding_subtype_val
  range_eq := Subtype.range_coe

/-- The level `{p₀² = 16/25}` is the frontier of the punctured `ℝP³`. -/
theorem rp3_frontier_FXR :
    {x : projectiveThreeSpaceLift.{0}.Carrier | rp3Defining_FXR x = 0} =
      frontier rp3Set_FXR := by
  rw [← rp3Solid_FXR.boundary_eq]
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, le_of_eq hx⟩, rp3Set_isBoundaryPoint_iff_FXR.mpr hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact rp3Set_isBoundaryPoint_iff_FXR.mp hp

end GC.GraphManifold.Assembly
