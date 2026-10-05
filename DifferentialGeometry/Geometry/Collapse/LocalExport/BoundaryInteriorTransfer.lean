import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormRestriction
import DifferentialGeometry.Geometry.Collapse.NormalizedCenterData

/-!
# Local data across a partial isometry; the interior completion at `{d > 5}` (lane BDRY-1, G4)

Route-independent transfer kit for LC88 / BCP04 (any target manifold `M`, so it serves the interior
completion `(W°, ĝ)` as well as any closed extension of the carrier).

* For a partial diffeomorphism `Φ : N ⇀ M` isometric (for `g₁`, `h₁`) on an open subset `S` of its
  source: sectional bounds (`sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1`), balls inside
  `S` (`image_riemannianBallOf_of_isometricOnOpen_BDRY1`, compact `N`), distances on quarter balls
  (`riemannianEDistOf_of_isometricOnOpen_BDRY1`), ball volumes (`ballVolume_of_isometricOnOpen_BDRY1`,
  boundaryless target model) and curvature derivative norms of every order
  (`curvatureDerivativeNorm_of_isometricOnOpen_BDRY1`) are carried; constant rescaling keeps the
  isometry (`scaleMetric_isometric_BDRY1`). The restriction is `PartialDiffeomorph.restrict`.
* Region of a carrier: `{d(·, ∂W) > c}` is open (`isOpen_lt_distanceToBoundary_BDRY1`) and contains
  `B(p, r)` when `r + c ≤ d(p, ∂W)` (`riemannianBallOf_subset_lt_distanceToBoundary_BDRY1`).
* Interior completion (G2): on `regionFive_BDRY1 = {d > 5}` the inverse inclusion is isometric
  (`completion_isometric_region_BDRY1`), hence at `{d > 5}` the sectional bounds, the curvature
  derivative norms and (for `r ρ + 5 ≤ d`) the ball volumes of `ĝ` and of the normalized metric
  `ρ⁻² ĝ` are those of `g` and `ρ⁻² g` on `W` — the LPA01 data of BSA06 carried to `(W°, ĝ)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold Bundle
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section OpenIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space N] [T2Space M] in
/-- A partial diffeomorphism isometric on an open subset `S` of its source, restricted to `S`, is
isometric on its whole source. -/
theorem restrict_isometric_BDRY1 (g₁ : SmoothRiemannianMetric I N)
    (h₁ : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞) {S : Set N}
    (hS : IsOpen S)
    (hiso : ∀ x ∈ S, ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w)) :
    ∀ x ∈ (DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ S hS).source,
      ∀ v w : TangentSpace I x,
        g₁.inner x v w = h₁.inner (DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ S hS x)
          (mfderiv I J (DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ S hS) x v)
          (mfderiv I J (DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ S hS) x w) :=
  fun x hx v w => hiso x hx.2 v w

/-- **Sectional bounds** are carried at the points of an open set on which `Φ` is isometric. -/
theorem sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1 (g₁ : SmoothRiemannianMetric I N)
    (h₁ : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞) {S : Set N}
    (hS : IsOpen S) (hSs : S ⊆ Φ.source)
    (hiso : ∀ x ∈ S, ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {x : N} (hx : x ∈ S) {κ : ℝ} :
    SectionalBoundedBelowAt g₁ x κ ↔ SectionalBoundedBelowAt h₁ (Φ x) κ :=
  sectionalBoundedBelowAt_iff_of_isometricOn g₁ h₁
    (DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ S hS)
    (restrict_isometric_BDRY1 g₁ h₁ Φ hS hiso) ⟨hSs hx, hx⟩

omit [FiniteDimensional ℝ F] in
/-- **Balls** inside an open set on which `Φ` is isometric are mapped onto balls (compact `N`). -/
theorem image_riemannianBallOf_of_isometricOnOpen_BDRY1 [CompactSpace N]
    (g₁ : SmoothRiemannianMetric I N)
    (h₁ : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞) {S : Set N}
    (hSs : S ⊆ Φ.source)
    (hiso : ∀ x ∈ S, ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {p : N} {r : ℝ} (hball : riemannianBallOf g₁ p r ⊆ S) :
    Φ '' riemannianBallOf g₁ p r = riemannianBallOf h₁ (Φ p) r :=
  image_riemannianBallOf_eq_of_isometricOn g₁ h₁ Φ (hball.trans hSs)
    (fun x hx v => (hiso x (hball hx) v v).symm)

omit [FiniteDimensional ℝ F] in
/-- **Distances** on the quarter ball of a ball inside an open set on which `Φ` is isometric. -/
theorem riemannianEDistOf_of_isometricOnOpen_BDRY1 [CompactSpace N]
    (g₁ : SmoothRiemannianMetric I N)
    (h₁ : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞) {S : Set N}
    (hSs : S ⊆ Φ.source)
    (hiso : ∀ x ∈ S, ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {p : N} {r : ℝ} (hball : riemannianBallOf g₁ p r ⊆ S) {x y : N}
    (hx : x ∈ riemannianBallOf g₁ p (r / 4)) (hy : y ∈ riemannianBallOf g₁ p (r / 4)) :
    riemannianEDistOf h₁ (Φ x) (Φ y) = riemannianEDistOf g₁ x y :=
  riemannianEDistOf_map_eq_of_isometricOn g₁ h₁ Φ (hball.trans hSs)
    (fun z hz v => (hiso z (hball hz) v v).symm) hx hy

/-- **Ball volumes** inside an open set on which `Φ` is isometric are preserved (compact `N`,
boundaryless target model). -/
theorem ballVolume_of_isometricOnOpen_BDRY1 [CompactSpace N] [J.Boundaryless]
    [SigmaCompactSpace N] [SigmaCompactSpace M] (g₁ : SmoothRiemannianMetric I N)
    (h₁ : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞) {S : Set N}
    (hS : IsOpen S) (hSs : S ⊆ Φ.source)
    (hiso : ∀ x ∈ S, ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {p : N} {r : ℝ} (hball : riemannianBallOf g₁ p r ⊆ S) :
    ballVolume h₁ (Φ p) r = ballVolume g₁ p r :=
  ballVolume_eq_of_isometricOn g₁ h₁
    (DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ S hS)
    (restrict_isometric_BDRY1 g₁ h₁ Φ hS hiso) (fun _ hz => ⟨hSs (hball hz), hball hz⟩)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space N] [T2Space M] in
/-- Constant rescaling preserves an isometry identity. -/
theorem scaleMetric_isometric_BDRY1 (g₁ : SmoothRiemannianMetric I N)
    (h₁ : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞) {S : Set N}
    (hiso : ∀ x ∈ S, ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {c : ℝ} (hc : 0 < c) :
    ∀ x ∈ S, ∀ v w : TangentSpace I x,
      (scaleMetric c hc g₁).inner x v w =
        (scaleMetric c hc h₁).inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
  intro x hx v w
  rw [scaleMetric_inner, scaleMetric_inner, hiso x hx v w]

/-- **Curvature derivative norms** are carried at the points of an open set on which `Φ` is
isometric. -/
theorem curvatureDerivativeNorm_of_isometricOnOpen_BDRY1 [SigmaCompactSpace N]
    (g₁ : SmoothRiemannianMetric I N)
    (h₁ : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞)
    (S : TopologicalSpace.Opens N) (hSs : (S : Set N) ⊆ Φ.source)
    (hiso : ∀ x ∈ S, ∀ v w : TangentSpace I x,
      g₁.inner x v w = h₁.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (k : ℕ) {x : N} (hx : x ∈ S) :
    curvatureDerivativeNorm g₁ k x = curvatureDerivativeNorm h₁ k (Φ x) := by
  have : SigmaCompactSpace S := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I S.isOpen)
  have hf : IsLocalDiffeomorph I J ∞ (fun y : S => Φ y.val) :=
    isLocalDiffeomorph_restrict_open S (fun y => ⟨Φ, hSs y.2, fun _ _ => rfl⟩)
  have hinj : Injective (fun y : S => Φ y.val) := fun a b hab =>
    Subtype.ext (Φ.injOn (hSs a.2) (hSs b.2) hab)
  have hd : ∀ (y : S) (v : TangentSpace I y),
      mfderiv I J (fun y : S => Φ y.val) y v = mfderiv I J Φ y.val v := by
    intro y v
    have hΦd : MDifferentiableAt I J Φ y.val :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hSs y.2))).mdifferentiableAt
        (by decide)
    have hval : MDifferentiableAt I I (Subtype.val : S → N) y :=
      ((contMDiff_subtype_val (I := I) (U := S)).contMDiffAt).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp := mfderiv_comp (I' := I) y hΦd hval
    change mfderiv I J (Φ ∘ Subtype.val) y v = _
    rw [hcomp, ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
  have hmet : ∀ (y : S) (v w : TangentSpace I y),
      (g₁.restrictOpen S).inner y v w =
        h₁.inner ((fun y : S => Φ y.val) y) (mfderiv I J (fun y : S => Φ y.val) y v)
          (mfderiv I J (fun y : S => Φ y.val) y w) := by
    intro y v w
    rw [hd y v, hd y w]
    exact hiso y.val y.2 v w
  have h1 := curvatureDerivativeNorm_of_injective_local_isometry (g₁.restrictOpen S) h₁
    (fun y : S => Φ y.val) hf hinj hmet k ⟨x, hx⟩
  rw [curvatureDerivativeNorm_restrictOpen] at h1
  exact h1

end OpenIsometry

/-! ## The region `{d > c}` of a carrier -/

section Region

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- `{d(·, ∂W) > c}` is open. -/
theorem isOpen_lt_distanceToBoundary_BDRY1 (c : ℝ) :
    IsOpen {x : W.Carrier | ENNReal.ofReal c < distanceToBoundary W g x} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨r, hr0, hcr, hrx⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have hmax : ENNReal.ofReal (max c 0) = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  have hcr' : max c 0 < r :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_max_right c 0)).mp (hmax ▸ hcr)
  set ε := r - max c 0 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  refine ⟨riemannianBallOf g x ε, fun y hy => ?_,
    isOpen_lt (continuous_riemannianEDist g x) continuous_const, ?_⟩
  · change ENNReal.ofReal c < distanceToBoundary W g y
    by_contra hle
    push Not at hle
    have hxy : riemannianEDistOf g x y < ENNReal.ofReal ε := hy
    have htri := distanceToBoundary_le_add W g x y
    have hlt : distanceToBoundary W g y + riemannianEDistOf g x y <
        ENNReal.ofReal (max c 0) + ENNReal.ofReal ε := by
      rw [hmax]
      exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
        hle hxy
    rw [← ENNReal.ofReal_add (le_max_right c 0) hεpos.le, hε, add_sub_cancel] at hlt
    exact (lt_irrefl _) ((hrx.trans_le htri).trans hlt)
  · change riemannianEDistOf g x x < ENNReal.ofReal ε
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hεpos

/-- A ball `B(p, r)` with `r + c ≤ d(p, ∂W)` (`r, c ≥ 0`) lies in `{d > c}`. -/
theorem riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 {p : W.Carrier} {r c : ℝ}
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hp : ENNReal.ofReal (r + c) ≤ distanceToBoundary W g p) :
    riemannianBallOf g p r ⊆ {x | ENNReal.ofReal c < distanceToBoundary W g x} := by
  intro x hx
  change ENNReal.ofReal c < distanceToBoundary W g x
  by_contra hle
  push Not at hle
  have hpx : riemannianEDistOf g p x < ENNReal.ofReal r := hx
  have htri := distanceToBoundary_le_add W g p x
  have hlt : distanceToBoundary W g x + riemannianEDistOf g p x <
      ENNReal.ofReal c + ENNReal.ofReal r :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle) hle hpx
  rw [← ENNReal.ofReal_add hc hr, add_comm c r] at hlt
  exact (lt_irrefl _) ((hp.trans htri).trans_lt hlt)

end Region

/-! ## The interior completion: local data at `{d > 5}` -/

section Completion

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

variable (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- The region `{d > 5}` as an open set. -/
def regionFive_BDRY1 : TopologicalSpace.Opens W.Carrier :=
  ⟨{x | ENNReal.ofReal 5 < distanceToBoundary W g x}, isOpen_lt_distanceToBoundary_BDRY1 W g 5⟩

/-- The inverse of the inclusion is isometric from `(g, ĝ)`, and from their normalizations by any
constant, on `{d > 5}`, which lies in its source. -/
theorem completion_isometric_region_BDRY1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) :
    have := connectedSpace_pieceInterior_top_BDRY1 W
    ((regionFive_BDRY1 W g : Set W.Carrier) ⊆ (interiorInclusion_BDRY1 W).symm.source) ∧
    ∀ x ∈ (regionFive_BDRY1 W g : Set W.Carrier), ∀ v w : TangentSpace W.model x,
      g.inner x v w = ĝ.inner ((interiorInclusion_BDRY1 W).symm x)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x v)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x w) := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  refine ⟨fun x hx => mem_interiorInclusion_target_BDRY1 W
    (mem_interior_of_distanceToBoundary_pos_BDRY1 W g (lt_of_le_of_lt zero_le hx)),
    fun x hx v w => (interiorInclusion_symm_isometric_of_eq_BDRY1 W g ĝ heq hx v w).symm⟩

/-- **Sectional bounds of the completion** at `{d > 5}`, for `ĝ` and for the normalized metrics
`ρ⁻² ĝ`, `ρ⁻² g` (any `ρ > 0`). -/
theorem sectionalBoundedBelowAt_completion_iff_BDRY1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    {ρ : ℝ} (hρ : 0 < ρ) (x : W.pieceInterior ⊤)
    (hx : ENNReal.ofReal 5 < distanceToBoundary W g x) (κ : ℝ) :
    (SectionalBoundedBelowAt ĝ x κ ↔ SectionalBoundedBelowAt g x.val κ) ∧
      (SectionalBoundedBelowAt (normalizedCenterMetric ĝ ρ hρ) x κ ↔
        SectionalBoundedBelowAt (normalizedCenterMetric g ρ hρ) x.val κ) := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨hsrc, hiso⟩ := completion_isometric_region_BDRY1 W g ĝ heq
  have hx' : x.val ∈ (regionFive_BDRY1 W g : Set W.Carrier) := hx
  have hΦx := interiorInclusion_symm_val_BDRY1 W x
  have h1 := sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1 g ĝ
    (interiorInclusion_BDRY1 W).symm (regionFive_BDRY1 W g).isOpen hsrc hiso hx' (κ := κ)
  have h2 := sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1 (normalizedCenterMetric g ρ hρ)
    (normalizedCenterMetric ĝ ρ hρ) (interiorInclusion_BDRY1 W).symm
    (regionFive_BDRY1 W g).isOpen hsrc
    (scaleMetric_isometric_BDRY1 g ĝ _ hiso (inv_pos.mpr (sq_pos_of_pos hρ))) hx' (κ := κ)
  rw [hΦx] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- **Curvature derivative norms of the completion** at `{d > 5}`, for `ĝ` and the normalized
metrics. -/
theorem curvatureDerivativeNorm_completion_eq_BDRY1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    {ρ : ℝ} (hρ : 0 < ρ) (x : W.pieceInterior ⊤)
    (hx : ENNReal.ofReal 5 < distanceToBoundary W g x) (k : ℕ) :
    curvatureDerivativeNorm ĝ k x = curvatureDerivativeNorm g k x.val ∧
      curvatureDerivativeNorm (normalizedCenterMetric ĝ ρ hρ) k x =
        curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k x.val := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨hsrc, hiso⟩ := completion_isometric_region_BDRY1 W g ĝ heq
  have hx' : x.val ∈ (regionFive_BDRY1 W g : Set W.Carrier) := hx
  have hΦx := interiorInclusion_symm_val_BDRY1 W x
  have h1 := curvatureDerivativeNorm_of_isometricOnOpen_BDRY1 g ĝ
    (interiorInclusion_BDRY1 W).symm (regionFive_BDRY1 W g) hsrc hiso k hx'
  have h2 := curvatureDerivativeNorm_of_isometricOnOpen_BDRY1 (normalizedCenterMetric g ρ hρ)
    (normalizedCenterMetric ĝ ρ hρ) (interiorInclusion_BDRY1 W).symm (regionFive_BDRY1 W g) hsrc
    (scaleMetric_isometric_BDRY1 g ĝ _ hiso (inv_pos.mpr (sq_pos_of_pos hρ))) k hx'
  rw [hΦx] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- **Ball volumes of the completion**: if `r ρ + 5 ≤ d(q, ∂W)` (`r ≥ 0`), the `ĝ`-ball of radius
`r ρ` and the normalized `ρ⁻² ĝ`-ball of radius `r` about `q` have the volumes of the corresponding
balls of `W`. -/
theorem ballVolume_completion_eq_BDRY1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    {ρ : ℝ} (hρ : 0 < ρ) (q : W.pieceInterior ⊤) {r : ℝ} (hr : 0 ≤ r)
    (hq : ENNReal.ofReal (r * ρ + 5) ≤ distanceToBoundary W g q) :
    ballVolume ĝ q (r * ρ) = ballVolume g q.val (r * ρ) ∧
      ballVolume (normalizedCenterMetric ĝ ρ hρ) q r =
        ballVolume (normalizedCenterMetric g ρ hρ) q.val r := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨hsrc, hiso⟩ := completion_isometric_region_BDRY1 W g ĝ heq
  have hΦx := interiorInclusion_symm_val_BDRY1 W q
  have hball : riemannianBallOf g q.val (r * ρ) ⊆ (regionFive_BDRY1 W g : Set W.Carrier) :=
    riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g (mul_nonneg hr hρ.le)
      (by norm_num) hq
  have hballN : riemannianBallOf (normalizedCenterMetric g ρ hρ) q.val r ⊆
      (regionFive_BDRY1 W g : Set W.Carrier) := by
    rw [normalizedCenterMetric_ball]
    exact hball
  have h1 := ballVolume_of_isometricOnOpen_BDRY1 g ĝ (interiorInclusion_BDRY1 W).symm
    (regionFive_BDRY1 W g).isOpen hsrc hiso hball
  have h2 := ballVolume_of_isometricOnOpen_BDRY1 (normalizedCenterMetric g ρ hρ)
    (normalizedCenterMetric ĝ ρ hρ) (interiorInclusion_BDRY1 W).symm
    (regionFive_BDRY1 W g).isOpen hsrc
    (scaleMetric_isometric_BDRY1 g ĝ _ hiso (inv_pos.mpr (sq_pos_of_pos hρ))) hballN
  rw [hΦx] at h1 h2
  exact ⟨h1, h2⟩

end Completion

end DifferentialGeometry.Geometry.Collapse
