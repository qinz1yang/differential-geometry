import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereZero
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormRP3Pieces

/-!
# FC39 producer, packet P0 (gate 1), §7.1: the S³ slim kind (one `S² × [0, 1]`)

Task-47 draft §7.1 / §7.9 rows "slim finite / model / disjoint", "slim end labels / functions" for
the S³ inhabitant (disposition D10), in the stereographic convention of `FC39P0SphereZero.lean`
(pole `e₀`, `r = ‖y‖`, `q₀ = (r² − 4)/(r² + 4)`):

* the slim piece `S = {1/2 ≤ r ≤ 1} = {−15/17 ≤ q₀ ≤ −3/5}` is the generic `S² × [0, 1]` piece
  `sphereIntervalPiece` (`AssemblyNormRP3Pieces.lean`) of `(z, s) ↦ ambient(((1 + s)/2) z)`, with
  the model `SlimModel.sphereInterval`;
* its two actual ends are the model faces `S² × {0}`, `S² × {1}` (the model boundary of the
  half-space product is `S² × {0, 1}`); the end `false = 0` (the sphere `r = 1/2`) is SHARED with
  the model boundary face of `Z₋ = sphereInnerBall` (`sphereSlim_shared_eq`: the two ambient sets
  are equal); the end `true = 1` (the sphere `r = 1`) is NEW (a face of `M₂ = {1 ≤ r ≤ 4}`), with
  `endFn = q₀ + 3/5` on `endNear = {q₀ > −15/17}` (regular zero set = the end, slim side `≤ 0`).

Result: `sphereSlimPieces : SlimPiecesV2 sphereW sphereZeroDomains sphereCuspCores`, and the
`shared_eq` clause of `JunctionsV2` for these data (`sphereSlim_shared_eq`).

Common S³ configuration (lead decision T49-1; labels recorded in `state-FC39-P0c.md`):
`Z₋ = {r ≤ 1/2}` (zero index 0), `S = {1/2 ≤ r ≤ 1}` (slim index 0), `M₂ = {1 ≤ r ≤ 4}`,
`Z₊ = {r ≥ 4}` (zero index 1); the handle end disks of `sphereEdgeBundle` at `r = 1` lie in the
new slim end, those at `r = 4` in the model face of `Z₊`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance ballChartsSlim_FC39P0c : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance closureSphereConnected_FC39P0c : ConnectedSpace ClosureSphere.{0} :=
  have hS : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

/-! ## The slim map `(z, s) ↦ ambient(((1 + s)/2) z)` -/

/-- The radial slim parametrization `(z, s) ↦ ((1 + s)/2) z` of the shell `1/2 ≤ ‖y‖ ≤ 1`. -/
def slimRadial (p : ClosureSphere.{0} × Icc (0 : ℝ) 1) : E3 :=
  (1 / 2 : ℝ) • pushShellRadial 1 (PieceEmbedding.sphereIccDown p)

theorem slimRadial_apply (p : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    slimRadial p = ((1 + (p.2 : ℝ)) / 2) • (p.1.down : E3) := by
  rw [slimRadial, PieceEmbedding.sphereIccDown_apply, pushShellRadial, smul_smul, one_mul]
  congr 1
  ring

theorem norm_slimRadial (p : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    ‖slimRadial p‖ = (1 + (p.2 : ℝ)) / 2 := by
  rw [slimRadial, norm_smul, PieceEmbedding.sphereIccDown_apply, norm_pushShellRadial zero_le_one]
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

theorem contMDiff_slimRadial : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ slimRadial :=
  (contDiff_const_smul (1 / 2 : ℝ)).contMDiff.comp
    ((contMDiff_pushShellRadial 1).comp PieceEmbedding.sphereIccDown.contMDiff)

theorem mfderiv_slimRadial_bijective (p : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) slimRadial p) := by
  let R : ClosureSphere.{0} × Icc (0 : ℝ) 1 → E3 := pushShellRadial 1 ∘ PieceEmbedding.sphereIccDown
  have hR : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ R :=
    (contMDiff_pushShellRadial 1).comp PieceEmbedding.sphereIccDown.contMDiff
  have hRb : Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) R p) := by
    rw [mfderiv_comp p ((contMDiff_pushShellRadial 1).mdifferentiableAt (by simp))
      (PieceEmbedding.sphereIccDown.contMDiff.mdifferentiableAt (by simp))]
    exact (mfderiv_pushShellRadial_bijective one_pos _).comp
      (PieceEmbedding.sphereIccDown.mfderivToContinuousLinearEquiv (by simp) p).bijective
  have hs : HasMFDerivAt (𝓡 3) (𝓡 3) (fun y : E3 => (1 / 2 : ℝ) • y) (R p)
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ E3) :=
    ((hasFDerivAt_id (R p)).const_smul (1 / 2 : ℝ)).hasMFDerivAt
  have hcomp : slimRadial = (fun y : E3 => (1 / 2 : ℝ) • y) ∘ R := rfl
  rw [hcomp, mfderiv_comp p hs.mdifferentiableAt (hR.mdifferentiableAt (by simp)), hs.mfderiv]
  have hb : Bijective ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ E3) := by
    constructor
    · intro v w h
      have h' : (1 / 2 : ℝ) • v = (1 / 2 : ℝ) • w := h
      exact smul_right_injective E3 (by norm_num : (1 / 2 : ℝ) ≠ 0) h'
    · intro v
      refine ⟨(2 : ℝ) • v, ?_⟩
      change (1 / 2 : ℝ) • (2 : ℝ) • v = v
      rw [smul_smul]
      norm_num
  exact hb.comp hRb

theorem slimRadial_injective : Injective slimRadial := by
  intro p q h
  have h1 : pushShellRadial 1 (PieceEmbedding.sphereIccDown p) =
      pushShellRadial 1 (PieceEmbedding.sphereIccDown q) :=
    smul_right_injective E3 (by norm_num : (1 / 2 : ℝ) ≠ 0) h
  obtain ⟨h2, h3⟩ := Prod.mk.inj (pushShellRadial_injective one_pos h1)
  exact Prod.ext (ULift.ext h2) h3

/-- Every vector of norm in `[1/2, 1]` is a radial slim point, with parameter `2‖y‖ − 1`. -/
theorem exists_slimRadial {y : E3} (h1 : 1 / 2 ≤ ‖y‖) (h2 : ‖y‖ ≤ 1) :
    ∃ p : ClosureSphere.{0} × Icc (0 : ℝ) 1, slimRadial p = y ∧ (p.2 : ℝ) = 2 * ‖y‖ - 1 := by
  have hy0 : ‖y‖ ≠ 0 := by linarith
  have hz : ‖y‖⁻¹ • y ∈ sphere (0 : E3) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy0]
  refine ⟨(ULift.up ⟨_, hz⟩, ⟨2 * ‖y‖ - 1, by linarith, by linarith⟩), ?_, rfl⟩
  rw [slimRadial_apply]
  change ((1 + (2 * ‖y‖ - 1)) / 2) • (‖y‖⁻¹ • y) = y
  rw [smul_smul]
  have : (1 + (2 * ‖y‖ - 1)) / 2 * ‖y‖⁻¹ = 1 := by
    field_simp
    ring
  rw [this, one_smul]

/-- The slim map into S³. -/
def slimMap (p : ClosureSphere.{0} × Icc (0 : ℝ) 1) : sphereW.Carrier :=
  cycleBallAmbient false (slimRadial p)

theorem contMDiff_slimMap : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) sphereW.model ∞ slimMap :=
  (cycleBallAmbient false).contMDiffOn_toFun.comp_contMDiff contMDiff_slimRadial
    fun p => by rw [cycleBallAmbient_source]; exact mem_univ _

theorem mfderiv_slimMap_bijective (p : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) sphereW.model slimMap p) := by
  have hsrc : slimRadial p ∈ (cycleBallAmbient false).source := by
    rw [cycleBallAmbient_source]
    exact mem_univ _
  have hcl := (cycleBallAmbient false).isLocalDiffeomorphAt _ _ ∞ hsrc
  have hcomp : slimMap = cycleBallAmbient false ∘ slimRadial := rfl
  rw [hcomp, mfderiv_comp p (hcl.mdifferentiableAt (by simp))
    (contMDiff_slimRadial.mdifferentiableAt (by simp))]
  exact (hcl.mfderivToContinuousLinearEquiv (by simp)).bijective.comp
    (mfderiv_slimRadial_bijective p)

theorem slimMap_injective : Injective slimMap := by
  intro p q h
  apply slimRadial_injective
  exact (cycleBallAmbient false).injOn (by rw [cycleBallAmbient_source]; exact mem_univ _)
    (by rw [cycleBallAmbient_source]; exact mem_univ _) h

/-! ## The slim piece and its height description -/

/-- **The slim piece `S`** (`S² × [0, 1]`, the shell `1/2 ≤ r ≤ 1`). -/
def sphereSlimPiece : PieceEmbedding sphereW :=
  sphereIntervalPiece slimMap contMDiff_slimMap mfderiv_slimMap_bijective slimMap_injective

/-- The `S² × [0, 1]` model of the slim piece. -/
def sphereSlimModel : SlimModel sphereSlimPiece :=
  .sphereInterval (sphereIntervalPieceDiffeo slimMap contMDiff_slimMap mfderiv_slimMap_bijective
    slimMap_injective)

theorem sphereHeight_slimMap (p : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    sphereHeight (slimMap p) = (‖slimRadial p‖ ^ 2 - 4) / (‖slimRadial p‖ ^ 2 + 4) :=
  sphereHeight_ambient_false _

/-- The stereographic height formula against a level, from below. -/
theorem le_stereoHeight_iff {t c : ℝ} (ht : 0 ≤ t) (hc : c < 1) :
    c ≤ (t - 4) / (t + 4) ↔ 4 * (1 + c) / (1 - c) ≤ t := by
  have hpos : (0 : ℝ) < t + 4 := by linarith
  have h1c : (0 : ℝ) < 1 - c := by linarith
  rw [le_div_iff₀ hpos, div_le_iff₀ h1c]
  constructor <;> intro h <;> nlinarith

/-- A point off the pole is in the chart image with the stereographic height of its norm. -/
theorem exists_ambient_of_height_lt {x : sphereW.Carrier} (hx : sphereHeight x < 1) :
    ∃ y, cycleBallAmbient false y = x ∧ sphereHeight x = (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
  have hne : spherePoint x ≠ cycleBallPole := by
    intro h
    rw [sphereHeight_eq_one_iff.2 h] at hx
    exact lt_irrefl _ hx
  obtain ⟨y, rfl⟩ := exists_ambient_false hne
  exact ⟨y, rfl, sphereHeight_ambient_false y⟩

theorem norm_le_one_iff_height {y : E3} :
    (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) ≤ -3 / 5 ↔ ‖y‖ ≤ 1 := by
  rw [stereoHeight_le_iff (sq_nonneg _) (by norm_num)]
  constructor
  · intro h
    nlinarith [norm_nonneg y]
  · intro h
    norm_num
    nlinarith [norm_nonneg y]

theorem half_le_norm_iff_height {y : E3} :
    -15 / 17 ≤ (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) ↔ 1 / 2 ≤ ‖y‖ := by
  rw [le_stereoHeight_iff (sq_nonneg _) (by norm_num)]
  constructor
  · intro h
    norm_num at h
    nlinarith [norm_nonneg y]
  · intro h
    norm_num
    nlinarith [norm_nonneg y]

/-- **The slim piece is the height band `−15/17 ≤ q₀ ≤ −3/5`.** -/
theorem range_slimMap :
    range slimMap = {x | -15 / 17 ≤ sphereHeight x ∧ sphereHeight x ≤ -3 / 5} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rw [mem_ofPred_eq, sphereHeight_slimMap, half_le_norm_iff_height, norm_le_one_iff_height,
      norm_slimRadial]
    constructor <;> linarith [p.2.2.1, p.2.2.2]
  · rintro ⟨h1, h2⟩
    obtain ⟨y, rfl, hy⟩ := exists_ambient_of_height_lt (by linarith : sphereHeight x < 1)
    rw [hy] at h1 h2
    obtain ⟨p, hp, -⟩ := exists_slimRadial (half_le_norm_iff_height.1 h1)
      (norm_le_one_iff_height.1 h2)
    exact ⟨p, by rw [slimMap, hp]⟩

/-- The height level of the slim end `b` (`−15/17` at `0`, `−3/5` at `1`). -/
def slimEndHeight (b : Bool) : ℝ :=
  bif b then -3 / 5 else -15 / 17

/-- **The end slices are height levels**: `q₀ = −15/17` at the end `0`, `q₀ = −3/5` at `1`. -/
theorem range_slimMap_end (b : Bool) :
    range (fun z => slimMap (z, iccEnd b)) = {x | sphereHeight x = slimEndHeight b} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [mem_ofPred_eq, sphereHeight_slimMap, norm_slimRadial]
    cases b <;> norm_num [iccEnd, slimEndHeight]
  · intro hx
    rw [mem_ofPred_eq] at hx
    have hlt : sphereHeight x < 1 := by
      rw [hx]
      cases b <;> norm_num [slimEndHeight]
    obtain ⟨y, rfl, hy⟩ := exists_ambient_of_height_lt hlt
    rw [hy] at hx
    have hy1 := (stereoHeight_eq_iff (sq_nonneg ‖y‖) (by cases b <;> norm_num [slimEndHeight])).1
      hx
    have hn : ‖y‖ = (1 + ((iccEnd b : Icc (0 : ℝ) 1) : ℝ)) / 2 := by
      have hpos : 0 ≤ (1 + ((iccEnd b : Icc (0 : ℝ) 1) : ℝ)) / 2 := by
        cases b <;> norm_num [iccEnd]
      refine (pow_left_inj₀ (norm_nonneg y) hpos two_ne_zero).1 ?_
      rw [hy1]
      cases b <;> norm_num [iccEnd, slimEndHeight]
    have hb1 : 1 / 2 ≤ ‖y‖ := by
      rw [hn]
      cases b <;> norm_num [iccEnd]
    have hb2 : ‖y‖ ≤ 1 := by
      rw [hn]
      cases b <;> norm_num [iccEnd]
    obtain ⟨p, hp, hp2⟩ := exists_slimRadial hb1 hb2
    have hpe : p.2 = iccEnd b := by
      apply Subtype.ext
      rw [hp2, hn]
      ring
    refine ⟨p.1, ?_⟩
    change cycleBallAmbient false (slimRadial (p.1, iccEnd b)) = cycleBallAmbient false y
    rw [← hpe, ← hp]

/-! ## The model boundary of the slim piece: the two end spheres -/

/-- The end sphere `S² × {b}` of the model `S² × [0, 1]`. -/
def slimEndSet (b : Bool) : Set (ClosureSphere.{0} × Icc (0 : ℝ) 1) :=
  range fun z => (z, iccEnd b)

theorem mem_slimEndSet {b : Bool} {p : ClosureSphere.{0} × Icc (0 : ℝ) 1} :
    p ∈ slimEndSet b ↔ p.2 = iccEnd b := by
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro h
    exact ⟨p.1, Prod.ext rfl h.symm⟩

theorem slimModelEnd_eq (b : Bool) : slimModelEnd sphereSlimModel b = slimEndSet b :=
  rfl

/-- **The model boundary of the slim piece is `S² × {0, 1}`.** -/
theorem slim_boundary_eq :
    (𝓡∂ 3).boundary sphereSlimPiece.Piece = slimEndSet false ∪ slimEndSet true := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have h1 := DifferentialGeometry.Manifold.euclideanHalfSpaceProd_boundary
    (ClosureSphere.{0} × Icc (0 : ℝ) 1)
  have h2 : ((𝓡 2).prod (𝓡∂ 1)).boundary (ClosureSphere.{0} × Icc (0 : ℝ) 1) =
      Set.prod univ ((𝓡∂ 1).boundary (Icc (0 : ℝ) 1)) :=
    ModelWithCorners.boundary_of_boundaryless_left
  refine h1.trans (h2.trans ?_)
  rw [boundary_Icc]
  ext p
  rw [mem_union, mem_slimEndSet, mem_slimEndSet]
  have hbot : (⊥ : Icc (0 : ℝ) 1) = iccEnd false := Subtype.ext (by simp [iccEnd])
  have htop : (⊤ : Icc (0 : ℝ) 1) = iccEnd true := Subtype.ext (by simp [iccEnd])
  constructor
  · rintro ⟨-, hp | hp⟩
    · exact Or.inl (hp.trans hbot)
    · exact Or.inr (hp.trans htop)
  · rintro (hp | hp)
    · exact ⟨mem_univ _, Or.inl (hp.trans hbot.symm)⟩
    · exact ⟨mem_univ _, Or.inr (hp.trans htop.symm)⟩

/-- The actual components of `S² × {0, 1}` are the two end spheres. -/
theorem connectedComponentIn_slimEnd (b : Bool) {x : ClosureSphere.{0} × Icc (0 : ℝ) 1}
    (hx : x ∈ slimEndSet b) :
    connectedComponentIn (slimEndSet false ∪ slimEndSet true) x = slimEndSet b := by
  have hpre : IsPreconnected (slimEndSet b) :=
    isPreconnected_range (continuous_id.prodMk continuous_const)
  have hsub : slimEndSet b ⊆ slimEndSet false ∪ slimEndSet true := by
    cases b
    exacts [subset_union_left, subset_union_right]
  refine Subset.antisymm ?_ (hpre.subset_connectedComponentIn hx hsub)
  have hcont : Continuous fun p : ClosureSphere.{0} × Icc (0 : ℝ) 1 => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hUV : Disjoint {p : ClosureSphere.{0} × Icc (0 : ℝ) 1 | (p.2 : ℝ) < 1 / 2}
      {p | 1 / 2 < (p.2 : ℝ)} :=
    Set.disjoint_left.2 fun p (h1 : (p.2 : ℝ) < 1 / 2) (h2 : 1 / 2 < (p.2 : ℝ)) =>
      lt_asymm h1 h2
  have hend : ∀ {p : ClosureSphere.{0} × Icc (0 : ℝ) 1} (c : Bool), p ∈ slimEndSet c →
      (p.2 : ℝ) = bif c then 1 else 0 := by
    intro p c hp
    rw [mem_slimEndSet] at hp
    rw [hp]
    cases c <;> rfl
  have hcov : connectedComponentIn (slimEndSet false ∪ slimEndSet true) x ⊆
      {p | (p.2 : ℝ) < 1 / 2} ∪ {p | 1 / 2 < (p.2 : ℝ)} := by
    intro p hp
    rcases connectedComponentIn_subset _ _ hp with h | h
    · left
      change (p.2 : ℝ) < 1 / 2
      rw [hend false h]
      norm_num
    · right
      change 1 / 2 < (p.2 : ℝ)
      rw [hend true h]
      norm_num
  have hxmem := mem_connectedComponentIn (hsub hx)
  have hxb := hend b hx
  rcases isPreconnected_connectedComponentIn.subset_or_subset (isOpen_lt hcont continuous_const)
    (isOpen_lt continuous_const hcont) hUV hcov with h | h
  · cases b
    · intro p hp
      rcases connectedComponentIn_subset _ _ hp with h' | h'
      · exact h'
      · have h1 : (p.2 : ℝ) < 1 / 2 := h hp
        rw [hend true h'] at h1
        norm_num at h1
    · have h1 : (x.2 : ℝ) < 1 / 2 := h hxmem
      rw [hxb] at h1
      norm_num at h1
  · cases b
    · have h1 : 1 / 2 < (x.2 : ℝ) := h hxmem
      rw [hxb] at h1
      norm_num at h1
    · intro p hp
      rcases connectedComponentIn_subset _ _ hp with h' | h'
      · have h1 : 1 / 2 < (p.2 : ℝ) := h hp
        rw [hend false h'] at h1
        norm_num at h1
      · exact h'

/-- A base point of the model sphere. -/
def slimSpherePoint : ClosureSphere.{0} :=
  ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩

theorem slimEnd_mem_boundary (b : Bool) :
    (slimSpherePoint, iccEnd b) ∈ (𝓡∂ 3).boundary sphereSlimPiece.Piece := by
  rw [slim_boundary_eq]
  cases b
  exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]

/-- **The actual model face of the slim end `b`** (the end sphere `S² × {b}`). -/
def slimEndFace (b : Bool) : ModelBoundaryFace sphereSlimPiece :=
  ⟨slimEndSet b, (slimSpherePoint, iccEnd b), slimEnd_mem_boundary b, by
    rw [slim_boundary_eq]
    exact (connectedComponentIn_slimEnd b ⟨_, rfl⟩).symm⟩

theorem slimEndFace_exhausted (F : ModelBoundaryFace sphereSlimPiece) :
    ∃ b, slimEndFace b = F := by
  obtain ⟨C, x, hx, rfl⟩ := F
  have hx' : x ∈ slimEndSet false ∪ slimEndSet true := by
    rw [← slim_boundary_eq]
    exact hx
  have key : ∀ b, x ∈ slimEndSet b → ∃ b', slimEndFace b' =
      ⟨connectedComponentIn ((𝓡∂ 3).boundary sphereSlimPiece.Piece) x, x, hx, rfl⟩ := by
    intro b hb
    refine ⟨b, Subtype.ext ?_⟩
    change slimEndSet b = connectedComponentIn ((𝓡∂ 3).boundary sphereSlimPiece.Piece) x
    rw [slim_boundary_eq]
    exact (connectedComponentIn_slimEnd b hb).symm
  rcases hx' with h | h
  exacts [key false h, key true h]

/-! ## The zero face shared with `Z₋` -/

theorem isPreconnected_innerBall_boundary :
    IsPreconnected ((𝓡∂ 3).boundary sphereInnerBall.Piece) := by
  have hS : PreconnectedSpace (Metric.sphere (0 : E3) 1) :=
    (isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)).toPreconnectedSpace
  have hR : IsPreconnected (range fun v : Metric.sphere (0 : E3) 1 =>
      (⟨v.val, (norm_eq_of_mem_sphere v).le⟩ : ClosedCell 3)) :=
    isPreconnected_range (continuous_subtype_val.subtype_mk _)
  have heq : (range fun v : Metric.sphere (0 : E3) 1 =>
      (⟨v.val, (norm_eq_of_mem_sphere v).le⟩ : ClosedCell 3)) =
      (𝓡∂ 3).boundary sphereInnerBall.Piece := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact closedCell_isBoundaryPoint_iff.2 (norm_eq_of_mem_sphere v)
    · intro hx
      exact ⟨⟨x.val, mem_sphere_zero_iff_norm.2 (closedCell_isBoundaryPoint_iff.1 hx)⟩, rfl⟩
  exact heq ▸ hR

/-- A boundary point of the closed ball. -/
def ballBoundaryPoint : ClosedCell 3 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

theorem ballBoundaryPoint_mem : ballBoundaryPoint ∈ (𝓡∂ 3).boundary sphereInnerBall.Piece :=
  closedCell_isBoundaryPoint_iff.2 (by simp [ballBoundaryPoint])

/-- **The model face of `Z₋`** (its whole boundary sphere). -/
def innerBallFace : ModelBoundaryFace sphereInnerBall :=
  ⟨(𝓡∂ 3).boundary sphereInnerBall.Piece, ballBoundaryPoint, ballBoundaryPoint_mem,
    (isPreconnected_innerBall_boundary.connectedComponentIn ballBoundaryPoint_mem).symm⟩

/-- The neighbour face of the shared slim end: the model face of `Z₋`. -/
def slimSharedNeighbour : NeighbourFace sphereZeroDomains sphereCuspCores :=
  .inl ⟨(0 : Fin 2), innerBallFace⟩

/-! ## The new end function -/

/-- The near set `{q₀ > −15/17}` of the new end. -/
def slimNear : TopologicalSpace.Opens sphereW.Carrier :=
  ⟨{x | -15 / 17 < sphereHeight x}, isOpen_lt continuous_const contMDiff_sphereHeight.continuous⟩

theorem slimEndFn_mfderiv (x : sphereW.Carrier) (hx : sphereHeight x + 3 / 5 = 0) :
    mfderiv sphereW.model 𝓘(ℝ, ℝ) (fun x => sphereHeight x + 3 / 5) x ≠ 0 := by
  have hlt : |sphereHeight x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hS := (contMDiff_sphereHeight x).mdifferentiableAt (by simp) |>.hasMFDerivAt
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t + 3 / 5) (sphereHeight x)
      (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id (sphereHeight x)).add_const (3 / 5 : ℝ)).hasMFDerivAt
  have hd := (hg.comp x hS).mfderiv
  change mfderiv sphereW.model 𝓘(ℝ, ℝ) ((fun t : ℝ => t + 3 / 5) ∘ sphereHeight) x ≠ 0
  rw [hd]
  exact mfderiv_sphereHeight_ne_zero hlt

theorem image_slimMap_end (b : Bool) :
    sphereSlimPiece.map '' slimModelEnd sphereSlimModel b =
      {x | sphereHeight x = slimEndHeight b} := by
  rw [← range_slimMap_end b, slimModelEnd_eq]
  ext x
  constructor
  · rintro ⟨p, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(z, iccEnd b), ⟨z, rfl⟩, rfl⟩

/-! ## The slim pieces of the S³ inhabitant -/

/-- **The slim pieces of the S³ inhabitant** (§5.3): one `S² × [0, 1]`; the end `0` shared with
the model face of `Z₋`, the end `1` new with `endFn = q₀ + 3/5` on `{q₀ > −15/17}`. -/
def sphereSlimPieces : SlimPiecesV2 sphereW sphereZeroDomains sphereCuspCores where
  count := 1
  piece _ := sphereSlimPiece
  model _ := sphereSlimModel
  disjoint j j' h := absurd (Subsingleton.elim j j') h
  endFace e := slimEndFace e.1.2
  endFace_eq _ := rfl
  endFace_exhausted _ F := by
    obtain ⟨b, hb⟩ := slimEndFace_exhausted F
    exact ⟨b, trivial, hb⟩
  endKind e := bif e.1.2 then none else some slimSharedNeighbour
  endFn _ x := sphereHeight x + 3 / 5
  endNear _ := slimNear
  endNear_interior _ _ _ := BoundarylessManifold.isInteriorPoint
  endFn_smooth _ := (contMDiff_sphereHeight.add contMDiff_const).contMDiffOn
  endFn_regular _ x _ h0 := slimEndFn_mfderiv x h0
  endFn_level := by
    rintro ⟨⟨⟨j, b⟩, hj⟩, hb⟩
    cases b
    · exact absurd hb (Option.some_ne_none _)
    · change sphereSlimPiece.map '' slimModelEnd sphereSlimModel true = _
      rw [image_slimMap_end]
      ext x
      simp only [slimEndHeight, Bool.cond_true, mem_ofPred_eq]
      constructor
      · intro hx
        refine ⟨?_, by linarith⟩
        change -15 / 17 < sphereHeight x
        linarith
      · rintro ⟨-, hx⟩
        linarith
  endFn_eq := by
    rintro ⟨⟨⟨j, b⟩, hj⟩, hb⟩
    change range slimMap ∩ slimNear = _
    rw [range_slimMap]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, by linarith⟩
    · rintro ⟨h3, h2⟩
      have h3' : -15 / 17 < sphereHeight x := h3
      exact ⟨⟨h3'.le, by linarith⟩, h3⟩

/-- **The shared end equals the neighbour face** (the `shared_eq` clause of `JunctionsV2` for the
S³ data): the end sphere `r = 1/2` of the slim piece is the model boundary image of `Z₋`. -/
theorem sphereSlim_shared_eq (e : sphereSlimPieces.End)
    (F : NeighbourFace sphereZeroDomains sphereCuspCores)
    (h : sphereSlimPieces.endKind e = some F) : sphereSlimPieces.endSet e = neighbourSet F := by
  obtain ⟨⟨j, b⟩, hj⟩ := e
  cases b
  · have hF : slimSharedNeighbour = F := Option.some_injective _ h
    subst hF
    change sphereSlimPiece.map '' slimModelEnd sphereSlimModel false =
      sphereInnerBall.map '' (𝓡∂ 3).boundary sphereInnerBall.Piece
    rw [image_slimMap_end]
    change _ = pieceBoundary sphereInnerBall
    rw [pieceBoundary_innerBall]
    ext x
    simp only [slimEndHeight, Bool.cond_false, mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  · exact absurd h.symm (Option.some_ne_none F)

end GC.GraphManifold.Assembly.FC39P0
