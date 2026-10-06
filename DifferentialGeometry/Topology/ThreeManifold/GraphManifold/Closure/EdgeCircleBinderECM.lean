import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeCircleSublevelECM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeCircleProductKernelECM
import DifferentialGeometry.Topology.Manifold.ImmersionRange
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.CircleLiftField
import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSliceCharts

/-!
# E4 binder: the hypotheses of the circle product kernel from an edge bundle

Draft 74, package E4. For `P : EdgeBundle W` and a smooth embedding `g : Circle → P.Base` (a circle
component of the edge base, `circleBase j` of `EdgeComponentModels`), everything that the abstract
kernel `edge_circle_product_kernel_ECM` needs, for the total space
`TotalC_ECM g = N = {x ∈ source | proj x ∈ range g ∧ height x ≤ level}` (the sublevel manifold of
`EdgeCircleSublevelECM.lean`):

* `circleDiffeo_ECM`: `Circle ≃ₘ range g` (the range is open and compact: an embedding of a
  circle into a one-manifold), `projCircle_ECM` / `totalProj_ECM` the circle-valued projection of
  the part of the source over `range g` / of the total space, its smoothness, its submersion
  property (from `proj_submersion`) and the characterization `totalProj x = z ↔ proj x = g z`;
* `liftDisk_ECM`: the lift of a fibre disk of `fibre_disk` into the total space (smooth by the
  universal property), its range is the fibre of `totalProj`;
* `connectedSpace_totalC_ECM`: the total space is connected (the projection is a closed quotient
  map with connected fibres);
* `exists_boundaryCurve_ECM`: the curve form of the submersion on the boundary: through every
  boundary point of the total space runs a smooth boundary curve with nonzero circle velocity.
  Route: the local angle of `projCircle`, the submersion coordinates of `(angle, height)` at the
  point (rank two of the edge bundle) and the straight line in the angle direction, reparametrized
  by `r sin (s / r)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

local instance diskChartsBinder_ECM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothBinder_ECM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance closedCellNonemptyBinder_ECM : Nonempty (ClosedCell 2) :=
  ⟨closedCellCenter 2⟩

namespace GC.GraphManifold.Assembly.FC39P0

/-- The differential of a diffeomorphism is bijective at every point. -/
theorem mfderiv_diffeo_bijective_ECM {EN HN EN' HN' : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] [NormedAddCommGroup EN'] [NormedSpace ℝ EN']
    [TopologicalSpace HN'] {I : ModelWithCorners ℝ EN HN} {I' : ModelWithCorners ℝ EN' HN'}
    {N N' : Type*} [TopologicalSpace N] [ChartedSpace HN N] [TopologicalSpace N']
    [ChartedSpace HN' N'] (e : N ≃ₘ⟮I, I'⟯ N') (x : N) : Function.Bijective (mfderiv I I' e x) := by
  have h := (e.mfderivToContinuousLinearEquiv (by simp) x).bijective
  rwa [← ContinuousLinearEquiv.coe_coe, Diffeomorph.mfderivToContinuousLinearEquiv_coe] at h

namespace EdgeBundle

variable {W : CompactCarrier.{u}} {P : EdgeBundle W} {g : Circle → P.Base}

theorem isOpen_range_circleBase_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    IsOpen (range g) :=
  Manifold.isOpen_range_of_isSmoothEmbedding rfl hg

theorem isCompact_range_circleBase_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    IsCompact (range g) :=
  isCompact_range hg.contMDiff.continuous

/-- The open image of the circle base. -/
def circleOpen_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) : TopologicalSpace.Opens P.Base :=
  ⟨range g, isOpen_range_circleBase_ECM hg⟩

/-- The circle is diffeomorphic to the open image of its base parametrization. -/
def circleDiffeo_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ (circleOpen_ECM hg) :=
  hg.diffeomorphOfRangeEq (IsSmoothEmbedding.of_opens (I := 𝓡 1) (n := ∞) (circleOpen_ECM hg))
    (by rw [Subtype.range_coe]; rfl)

theorem val_circleDiffeo_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (z : Circle) :
    ((circleDiffeo_ECM hg z : circleOpen_ECM hg) : P.Base) = g z :=
  hg.comp_diffeomorphOfRangeEq (IsSmoothEmbedding.of_opens (I := 𝓡 1) (n := ∞) (circleOpen_ECM hg))
    (by rw [Subtype.range_coe]; rfl) z

variable (P) in
/-- The open part of the source over an open set of the base. -/
def underOpen_ECM (B : Set P.Base) (hB : IsOpen B) : TopologicalSpace.Opens P.source :=
  ⟨P.proj ⁻¹' B, hB.preimage P.proj.continuous⟩

/-- The part of the source over the circle component, as a manifold (open in the source). -/
abbrev underCircle_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    TopologicalSpace.Opens P.source :=
  P.underOpen_ECM (range g) (isOpen_range_circleBase_ECM hg)

/-- The projection of the part of the source over the circle component into the open image. -/
def projOpen_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (y : underCircle_ECM hg) :
    circleOpen_ECM hg :=
  ⟨P.proj y.1, y.2⟩

theorem contMDiff_projOpen_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    ContMDiff W.model (𝓡 1) ∞ (projOpen_ECM (P := P) hg) := by
  rw [← ContMDiff.subtypeVal_comp_iff (circleOpen_ECM hg)]
  exact P.proj_smooth.comp contMDiff_subtype_val

/-- The circle-valued projection of the part of the source over the circle component. -/
def projCircle_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (y : underCircle_ECM hg) : Circle :=
  (circleDiffeo_ECM hg).symm (projOpen_ECM hg y)

theorem contMDiff_projCircle_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    ContMDiff W.model (𝓡 1) ∞ (projCircle_ECM (P := P) hg) :=
  (circleDiffeo_ECM hg).symm.contMDiff.comp (contMDiff_projOpen_ECM hg)

theorem projCircle_eq_iff_ECM {hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g}
    {y : underCircle_ECM hg} {z : Circle} :
    projCircle_ECM hg y = z ↔ P.proj y.1 = g z := by
  unfold projCircle_ECM
  constructor
  · intro h
    have h' : projOpen_ECM hg y = circleDiffeo_ECM hg z := by
      rw [← h, Diffeomorph.apply_symm_apply]
    have := congrArg (fun o : circleOpen_ECM hg => (o : P.Base)) h'
    rw [val_circleDiffeo_ECM hg z] at this
    exact this
  · intro h
    have h' : projOpen_ECM hg y = circleDiffeo_ECM hg z :=
      Subtype.ext (h.trans (val_circleDiffeo_ECM hg z).symm)
    rw [h', Diffeomorph.symm_apply_apply]

theorem mfderiv_projOpen_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g)
    (y : underCircle_ECM hg) :
    mfderiv W.model (𝓡 1) (projOpen_ECM (P := P) hg) y = mfderiv W.model (𝓡 1) P.proj y.1 := by
  have h1 := DifferentialGeometry.mfderiv_subtypeVal_comp (I := W.model) (J := 𝓡 1)
    (U := circleOpen_ECM hg) (projOpen_ECM (P := P) hg) y
  have h2 := DifferentialGeometry.mfderiv_restrict_open (I := W.model) (J := 𝓡 1) P.proj
    (underCircle_ECM hg) y
  exact h1.symm.trans h2

theorem surjective_mfderiv_projCircle_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g)
    (y : underCircle_ECM hg) :
    Function.Surjective (mfderiv W.model (𝓡 1) (projCircle_ECM (P := P) hg) y) := by
  have hd1 : MDifferentiableAt W.model (𝓡 1) (projOpen_ECM (P := P) hg) y :=
    (contMDiff_projOpen_ECM hg y).mdifferentiableAt (by simp)
  have hd2 : MDifferentiableAt (𝓡 1) (𝓡 1) (circleDiffeo_ECM hg).symm (projOpen_ECM hg y) :=
    ((circleDiffeo_ECM hg).symm.contMDiff _).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y hd2 hd1
  have hbij := mfderiv_diffeo_bijective_ECM (circleDiffeo_ECM hg).symm (projOpen_ECM hg y)
  have hsurj : Function.Surjective (mfderiv W.model (𝓡 1) (projOpen_ECM (P := P) hg) y) := by
    rw [mfderiv_projOpen_ECM hg y]
    exact P.proj_submersion y.1
  change Function.Surjective (mfderiv W.model (𝓡 1)
    ((circleDiffeo_ECM hg).symm ∘ projOpen_ECM (P := P) hg) y)
  rw [hcomp, ContinuousLinearMap.coe_comp]
  exact hbij.surjective.comp hsurj

/-- The total space over the circle component. -/
abbrev TotalC_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) : Type u :=
  P.Total_ECM (isOpen_range_circleBase_ECM hg) (isCompact_range_circleBase_ECM hg)

/-- A point of the total space as a point of the part of the source over the circle component. -/
def toUnder_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (x : TotalC_ECM hg) :
    underCircle_ECM hg :=
  ⟨⟨x.1, P.total_mem_source_ECM x⟩, (mem_overOpen_ECM.mp (P.total_mem_overOpen_ECM x)).2⟩

theorem toUnder_val_val_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (x : TotalC_ECM hg) :
    (((toUnder_ECM hg x : underCircle_ECM hg) : P.source) : W.Carrier) = x.1 :=
  rfl

theorem contMDiff_toUnder_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    ContMDiff (𝓡∂ 3) W.model ∞ (toUnder_ECM (P := P) hg) := by
  rw [← ContMDiff.subtypeVal_comp_iff (underCircle_ECM hg)]
  rw [← ContMDiff.subtypeVal_comp_iff P.source]
  exact P.contMDiff_total_val_ECM

theorem mfderiv_toUnder_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (x : TotalC_ECM hg) :
    mfderiv (𝓡∂ 3) W.model (toUnder_ECM (P := P) hg) x =
      mfderiv (𝓡∂ 3) W.model (Subtype.val : TotalC_ECM hg → W.Carrier) x := by
  have h1 := DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡∂ 3) (J := W.model)
    (U := underCircle_ECM hg) (toUnder_ECM (P := P) hg) x
  have h2 := DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡∂ 3) (J := W.model)
    (U := P.source) (fun y => ((toUnder_ECM (P := P) hg y : underCircle_ECM hg) : P.source)) x
  exact h1.symm.trans h2.symm

/-- The circle-valued projection of the total space over the circle component. -/
def totalProj_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (x : TotalC_ECM hg) : Circle :=
  projCircle_ECM hg (toUnder_ECM hg x)

theorem contMDiff_totalProj_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    ContMDiff (𝓡∂ 3) (𝓡 1) ∞ (totalProj_ECM (P := P) hg) :=
  (contMDiff_projCircle_ECM hg).comp (contMDiff_toUnder_ECM hg)

theorem surjective_mfderiv_totalProj_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g)
    (x : TotalC_ECM hg) :
    Function.Surjective (mfderiv (𝓡∂ 3) (𝓡 1) (totalProj_ECM (P := P) hg) x) := by
  have hd1 : MDifferentiableAt (𝓡∂ 3) W.model (toUnder_ECM (P := P) hg) x :=
    (contMDiff_toUnder_ECM hg x).mdifferentiableAt (by simp)
  have hd2 : MDifferentiableAt W.model (𝓡 1) (projCircle_ECM (P := P) hg) (toUnder_ECM hg x) :=
    (contMDiff_projCircle_ECM hg _).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hd2 hd1
  have hbij : Function.Bijective (mfderiv (𝓡∂ 3) W.model (toUnder_ECM (P := P) hg) x) := by
    rw [mfderiv_toUnder_ECM hg x]
    exact P.mfderiv_total_val_bijective_ECM x
  change Function.Surjective (mfderiv (𝓡∂ 3) (𝓡 1)
    (projCircle_ECM (P := P) hg ∘ toUnder_ECM hg) x)
  rw [hcomp, ContinuousLinearMap.coe_comp]
  exact (surjective_mfderiv_projCircle_ECM hg _).comp hbij.surjective

theorem totalProj_eq_iff_ECM {hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g} {x : TotalC_ECM hg}
    {z : Circle} :
    totalProj_ECM hg x = z ↔ P.proj ⟨x.1, P.total_mem_source_ECM x⟩ = g z :=
  projCircle_eq_iff_ECM

/-! ## The fibre disks inside the total space -/

theorem mem_total_of_mem_disk_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) {z : Circle}
    {x : W.Carrier}
    (hx : x ∈ Subtype.val '' {y : P.source | P.proj y = g z ∧ P.height y ≤ P.level}) :
    P.sublevelFn_ECM (isOpen_range_circleBase_ECM hg) (isCompact_range_circleBase_ECM hg) x ≤
      P.level := by
  obtain ⟨y, ⟨hy1, hy2⟩, rfl⟩ := hx
  rw [sublevelFn_le_iff_ECM]
  exact ⟨mem_overOpen_ECM.mpr ⟨y.2, by rw [show (⟨y.1, y.2⟩ : P.source) = y from rfl, hy1]; exact
    ⟨z, rfl⟩⟩, by rw [heightExt_apply_ECM]; exact hy2⟩

/-- The lift of a disk over `z` into the total space. -/
def liftDisk_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) {z : Circle}
    {φ : ClosedCell 2 → W.Carrier}
    (hφ : range φ = Subtype.val '' {y : P.source | P.proj y = g z ∧ P.height y ≤ P.level})
    (w : ClosedCell 2) : TotalC_ECM hg :=
  ⟨φ w, mem_total_of_mem_disk_ECM hg (hφ ▸ mem_range_self w)⟩

theorem val_liftDisk_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) {z : Circle}
    {φ : ClosedCell 2 → W.Carrier}
    (hφ : range φ = Subtype.val '' {y : P.source | P.proj y = g z ∧ P.height y ≤ P.level})
    (w : ClosedCell 2) : (liftDisk_ECM hg hφ w).1 = φ w :=
  rfl

theorem contMDiff_liftDisk_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) {z : Circle}
    {φ : ClosedCell 2 → W.Carrier}
    (hφ : range φ = Subtype.val '' {y : P.source | P.proj y = g z ∧ P.height y ≤ P.level})
    (hφs : ContMDiff (𝓡∂ 2) W.model ∞ φ) :
    ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ (liftDisk_ECM hg hφ) :=
  P.contMDiff_total_iff_ECM.mpr hφs

theorem range_liftDisk_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) {z : Circle}
    {φ : ClosedCell 2 → W.Carrier}
    (hφ : range φ = Subtype.val '' {y : P.source | P.proj y = g z ∧ P.height y ≤ P.level}) :
    range (liftDisk_ECM hg hφ) = totalProj_ECM hg ⁻¹' {z} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    have hw : φ w ∈ range φ := mem_range_self w
    rw [hφ] at hw
    obtain ⟨y, ⟨hy1, -⟩, hyw⟩ := hw
    change totalProj_ECM hg (liftDisk_ECM hg hφ w) = z
    rw [totalProj_eq_iff_ECM]
    have : (⟨(liftDisk_ECM hg hφ w).1, P.total_mem_source_ECM _⟩ : P.source) = y :=
      Subtype.ext hyw.symm
    rw [this]
    exact hy1
  · intro hx
    have hx' : totalProj_ECM hg x = z := hx
    rw [totalProj_eq_iff_ECM] at hx'
    have hmem : x.1 ∈ range φ := by
      rw [hφ]
      exact ⟨⟨x.1, P.total_mem_source_ECM x⟩, ⟨hx',
        (P.heightExt_apply_ECM ⟨x.1, P.total_mem_source_ECM x⟩).symm.trans_le
          (P.total_heightExt_le_ECM x)⟩, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, Subtype.ext hw⟩

/-- The total space over the circle component is connected: the projection to the circle is a
closed quotient map with connected fibres (the fibre disks). -/
theorem connectedSpace_totalC_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) :
    ConnectedSpace (TotalC_ECM hg) := by
  have hcc : ConnectedSpace (ClosedCell 2) :=
    @ConnectedSpace.mk _ _ closedCell_two_preconnectedSpace ⟨closedCellCenter 2⟩
  have hfib : ∀ z, IsConnected (totalProj_ECM hg ⁻¹' {z}) := by
    intro z
    obtain ⟨φ, hφe, hφr⟩ := P.fibre_disk (g z)
    rw [← range_liftDisk_ECM hg hφr]
    exact isConnected_range (contMDiff_liftDisk_ECM hg hφr hφe.contMDiff).continuous
  have hsurj : Surjective (totalProj_ECM hg) := fun z => (hfib z).nonempty
  have hcont := (contMDiff_totalProj_ECM (P := P) hg).continuous
  have hq := hcont.isClosedMap.isQuotientMap hcont hsurj
  have h := hq.isCoinducing.isConnected_preimage_of_isClosed hfib isClosed_univ isConnected_univ
  rw [preimage_univ] at h
  exact connectedSpace_iff_univ.mpr h

/-! ## The boundary curves -/

theorem mfderiv_projCircle_eq_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g)
    (y : underCircle_ECM hg) :
    mfderiv W.model (𝓡 1) (projCircle_ECM (P := P) hg) y =
      (mfderiv (𝓡 1) (𝓡 1) (circleDiffeo_ECM hg).symm (projOpen_ECM hg y)).comp
        (mfderiv W.model (𝓡 1) P.proj y.1) := by
  have hd1 : MDifferentiableAt W.model (𝓡 1) (projOpen_ECM (P := P) hg) y :=
    (contMDiff_projOpen_ECM hg y).mdifferentiableAt (by simp)
  have hd2 : MDifferentiableAt (𝓡 1) (𝓡 1) (circleDiffeo_ECM hg).symm (projOpen_ECM hg y) :=
    ((circleDiffeo_ECM hg).symm.contMDiff _).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y hd2 hd1
  rw [mfderiv_projOpen_ECM hg y] at hcomp
  exact hcomp

theorem mfderiv_height_under_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g)
    (y : underCircle_ECM hg) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun q : underCircle_ECM hg => P.height q.1) y =
      mfderiv W.model 𝓘(ℝ, ℝ) P.height y.1 :=
  DifferentialGeometry.mfderiv_restrict_open (I := W.model) (J := 𝓘(ℝ, ℝ)) P.height
    (underCircle_ECM hg) y

theorem mfderiv_pair_ECM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X]
    [ChartedSpace H X] {θ κ : X → ℝ} {y : X} (h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) θ y)
    (h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) κ y) (v : E) :
    (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun q => (θ q, κ q)) y : E →L[ℝ] ℝ × ℝ) v =
      ((mfderiv I 𝓘(ℝ, ℝ) θ y : E →L[ℝ] ℝ) v, (mfderiv I 𝓘(ℝ, ℝ) κ y : E →L[ℝ] ℝ) v) := by
  have hQ : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (fun q => (θ q, κ q)) y :=
    h1.prodMk_space h2
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (θ y, κ y) := ((ContinuousLinearMap.fst ℝ ℝ ℝ).contMDiff (n := ∞)).mdifferentiableAt
        (by simp)
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (θ y, κ y) := ((ContinuousLinearMap.snd ℝ ℝ ℝ).contMDiff (n := ∞)).mdifferentiableAt
        (by simp)
  have hc1 := mfderiv_comp y hf hQ
  have hc2 := mfderiv_comp y hs hQ
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hc1 hc2
  refine Prod.ext ?_ ?_
  · have := congrArg (fun L => L v) hc1
    exact this.symm
  · have := congrArg (fun L => L v) hc2
    exact this.symm

theorem surjective_mfderiv_angleHeight_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g)
    (y : underCircle_ECM hg) {θ : underCircle_ECM hg → ℝ}
    (hθ : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ θ)
    (hev : ∀ᶠ q in 𝓝 y, Circle.exp (θ q) = projCircle_ECM hg q) (hy : P.height y.1 = P.level) :
    Function.Surjective
      (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun q => (θ q, P.height q.1)) y) := by
  have hpθ : projCircle_ECM hg =ᶠ[𝓝 y] fun q => Circle.exp (θ q) := by
    filter_upwards [hev] with q hq using hq.symm
  have hθd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) θ y := (hθ y).mdifferentiableAt (by simp)
  have hHd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun q : underCircle_ECM hg => P.height q.1) y :=
    (P.height_smooth.comp contMDiff_subtype_val y).mdifferentiableAt (by simp)
  let E3 := EuclideanSpace ℝ (Fin 3)
  let E1 := EuclideanSpace ℝ (Fin 1)
  let Lp : E3 →L[ℝ] E1 := mfderiv W.model (𝓡 1) P.proj y.1
  let Lh : E3 →L[ℝ] ℝ := mfderiv W.model 𝓘(ℝ, ℝ) P.height y.1
  let Lθ : E3 →L[ℝ] ℝ := mfderiv W.model 𝓘(ℝ, ℝ) θ y
  let Lpc : E3 →L[ℝ] E1 := mfderiv W.model (𝓡 1) (projCircle_ECM (P := P) hg) y
  let LH : E3 →L[ℝ] ℝ := mfderiv W.model 𝓘(ℝ, ℝ) (fun q : underCircle_ECM hg => P.height q.1) y
  let L : E1 →L[ℝ] E1 :=
    mfderiv (𝓡 1) (𝓡 1) (circleDiffeo_ECM hg).symm (projOpen_ECM hg y)
  let ℓ : ℝ →L[ℝ] E1 := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ y)
  have hrel : ∀ v : E3, Lpc v = ℓ (Lθ v) := fun v =>
    DifferentialGeometry.Manifold.BoundaryTangentFlow.mfderiv_apply_eq_of_local_angle hθd hpθ v
  have hLH : LH = Lh := mfderiv_height_under_ECM hg y
  have hLpc : Lpc = L.comp Lp := mfderiv_projCircle_eq_ECM hg y
  have hLinj : Function.Injective L := (mfderiv_diffeo_bijective_ECM _ _).injective
  obtain ⟨v₁, hv₁⟩ : ∃ v : E3, (Lp v, Lh v) = ((0 : E1), (1 : ℝ)) :=
    P.rank_two y.1 hy ((0 : E1), (1 : ℝ))
  obtain ⟨v₂, hv₂⟩ : ∃ v : E3,
      (Lp v, Lh v) = (EuclideanSpace.single (0 : Fin 1) (1 : ℝ), (0 : ℝ)) :=
    P.rank_two y.1 hy (EuclideanSpace.single (0 : Fin 1) (1 : ℝ), (0 : ℝ))
  have h1a : Lp v₁ = 0 := congrArg Prod.fst hv₁
  have h1b : Lh v₁ = 1 := congrArg Prod.snd hv₁
  have h2a : Lp v₂ = EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := congrArg Prod.fst hv₂
  have h2b : Lh v₂ = 0 := congrArg Prod.snd hv₂
  have hp1 : Lpc v₁ = 0 := by
    rw [hLpc, ContinuousLinearMap.comp_apply, h1a, map_zero]
  have hp2 : Lpc v₂ ≠ 0 := by
    rw [hLpc, ContinuousLinearMap.comp_apply, h2a]
    intro h0
    have h3 := hLinj (h0.trans (map_zero L).symm)
    have h00 := congrArg (fun z : E1 => z 0) h3
    simp at h00
  have hℓlin : ∀ t : ℝ, ℓ t = t • ℓ 1 := fun t => by
    conv_lhs => rw [show t = t • (1 : ℝ) by simp]
    exact map_smul ℓ t 1
  have hℓ1 : ℓ 1 ≠ 0 := by
    intro h0
    apply hp2
    rw [hrel v₂, hℓlin, h0, smul_zero]
  have hκ0 : Lθ v₂ ≠ 0 := by
    intro h0
    apply hp2
    rw [hrel v₂, h0, map_zero]
  have hθ1 : Lθ v₁ = 0 := by
    have h := hrel v₁
    rw [hp1, hℓlin] at h
    rcases smul_eq_zero.mp h.symm with h0 | h0
    · exact h0
    · exact absurd h0 hℓ1
  rintro ⟨a, b⟩
  refine ⟨(a / Lθ v₂) • v₂ + b • v₁, ?_⟩
  have hv : (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun q => (θ q, P.height q.1)) y : E3 →L[ℝ] ℝ × ℝ)
      ((a / Lθ v₂) • v₂ + b • v₁) =
      (Lθ ((a / Lθ v₂) • v₂ + b • v₁), LH ((a / Lθ v₂) • v₂ + b • v₁)) :=
    mfderiv_pair_ECM hθd hHd _
  refine hv.trans ?_
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, hLH, hθ1, h1b, h2b]
  refine Prod.ext ?_ ?_
  · simp only [smul_eq_mul, mul_zero, add_zero]
    field_simp
  · simp

/-- The differential of `Circle.exp` at the local angle of the projection is nonzero. -/
theorem mfderiv_exp_angle_ne_zero_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g)
    (y : underCircle_ECM hg) {θ : underCircle_ECM hg → ℝ}
    (hθ : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ θ)
    (hev : ∀ᶠ q in 𝓝 y, Circle.exp (θ q) = projCircle_ECM hg q) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ y) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) 1 ≠ 0 := by
  have hpθ : projCircle_ECM hg =ᶠ[𝓝 y] fun q => Circle.exp (θ q) := by
    filter_upwards [hev] with q hq using hq.symm
  have hθd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) θ y := (hθ y).mdifferentiableAt (by simp)
  let E3 := EuclideanSpace ℝ (Fin 3)
  let E1 := EuclideanSpace ℝ (Fin 1)
  let Lθ : E3 →L[ℝ] ℝ := mfderiv W.model 𝓘(ℝ, ℝ) θ y
  let Lpc : E3 →L[ℝ] E1 := mfderiv W.model (𝓡 1) (projCircle_ECM (P := P) hg) y
  let ℓ : ℝ →L[ℝ] E1 := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ y)
  have hrel : ∀ v : E3, Lpc v = ℓ (Lθ v) := fun v =>
    DifferentialGeometry.Manifold.BoundaryTangentFlow.mfderiv_apply_eq_of_local_angle hθd hpθ v
  have hℓlin : ∀ t : ℝ, ℓ t = t • ℓ 1 := fun t => by
    conv_lhs => rw [show t = t • (1 : ℝ) by simp]
    exact map_smul ℓ t 1
  intro h0
  have h0' : ℓ 1 = 0 := h0
  obtain ⟨v, hv⟩ : ∃ v : E3, Lpc v = EuclideanSpace.single (0 : Fin 1) (1 : ℝ) :=
    surjective_mfderiv_projCircle_ECM hg y (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  have h1 := hrel v
  rw [hℓlin, h0', smul_zero] at h1
  have h2 : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : E1) = 0 := hv.symm.trans h1
  have h00 := congrArg (fun z : E1 => z 0) h2
  simp at h00

/-- A point of the part of the source over the circle component, of height at most the level, as a
point of the total space. -/
def ofUnder_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (z : underCircle_ECM hg)
    (h : P.height z.1 ≤ P.level) : TotalC_ECM hg :=
  ⟨z.1.1, sublevelFn_le_iff_ECM.mpr ⟨mem_overOpen_ECM.mpr ⟨z.1.2, z.2⟩,
    (P.heightExt_apply_ECM z.1).trans_le h⟩⟩

theorem toUnder_ofUnder_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (z : underCircle_ECM hg)
    (h : P.height z.1 ≤ P.level) : toUnder_ECM hg (ofUnder_ECM hg z h) = z :=
  rfl

/-- **The boundary curves** (curve form of the submersion on the boundary): through every boundary
point of the total space runs a smooth curve inside the boundary along which the projection to the
circle has nonzero velocity. -/
theorem exists_boundaryCurve_ECM (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (x : TotalC_ECM hg)
    (hx : (𝓡∂ 3).IsBoundaryPoint x) :
    ∃ γ : ℝ → TotalC_ECM hg, ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = x ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (totalProj_ECM hg ∘ γ) 0 ≠ 0 := by
  set y : underCircle_ECM hg := toUnder_ECM hg x with hy
  have hlevel : P.height y.1 = P.level :=
    (P.heightExt_apply_ECM y.1).symm.trans (P.total_isBoundaryPoint_iff_ECM.mp hx)
  obtain ⟨θ, hθ, hev⟩ := DifferentialGeometry.Manifold.BoundaryTangentFlow.exists_local_angle
    (I := W.model) (projCircle_ECM hg) (contMDiff_projCircle_ECM hg) y
  have hHs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun q : underCircle_ECM hg => P.height q.1) :=
    P.height_smooth.comp contMDiff_subtype_val
  have hQ : ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞
      (fun q : underCircle_ECM hg => (θ q, P.height q.1)) := hθ.prodMk_space hHs
  have hint : W.model.IsInteriorPoint y :=
    W.model.isInteriorPoint_iff_isInteriorPoint_val.mpr
      (W.model.isInteriorPoint_iff_isInteriorPoint_val.mpr (P.source_interior y.1.2))
  obtain ⟨θc, hyθ, hθQ, hθ2⟩ :=
    DifferentialGeometry.Manifold.RegularLevel.exists_interior_submersion_coordinates hQ hint
      (surjective_mfderiv_angleHeight_ECM hg y hθ hev hlevel)
  have hc₀ : θc y = ((θ y, P.height y.1), (θc y).2) := Prod.ext (hθQ y hyθ) rfl
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp θc.open_target (θc y) (θc.map_source hyθ)
  set r : ℝ := ε₀ / 2 with hr
  have hr0 : 0 < r := by positivity
  let σ : ℝ → ℝ := fun s => r * Real.sin (s / r)
  have hσ0 : σ 0 = 0 := by simp [σ]
  have hσb : ∀ s, |σ s| < ε₀ := fun s => by
    have h1 : |Real.sin (s / r)| ≤ 1 := Real.abs_sin_le_one _
    calc |σ s| = r * |Real.sin (s / r)| := by simp [σ, abs_mul, abs_of_pos hr0]
      _ ≤ r * 1 := by gcongr
      _ < ε₀ := by rw [mul_one, hr]; linarith
  let pathc : ℝ → _ := fun s => ((((θc y).1.1 + σ s), (θc y).1.2), (θc y).2)
  have hpath0 : pathc 0 = θc y := by simp [pathc, hσ0]
  have hmem : ∀ s, pathc s ∈ θc.target := fun s => hball (by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
    simp only [pathc, dist_self, Real.dist_eq]
    simpa using hσb s)
  have hpathsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, type_of% (θc y)) ∞ pathc := by
    refine ContDiff.contMDiff ?_
    exact (((contDiff_const.add (contDiff_const.mul
      (Real.contDiff_sin.comp (contDiff_id.div_const r)))).prodMk contDiff_const).prodMk
      contDiff_const)
  let γ' : ℝ → underCircle_ECM hg := fun s => θc.symm (pathc s)
  have hγ'sm : ContMDiff 𝓘(ℝ, ℝ) W.model ∞ γ' :=
    θc.symm.contMDiffOn.comp_contMDiff hpathsm hmem
  have hγ'src : ∀ s, γ' s ∈ θc.source := fun s => θc.map_target (hmem s)
  have hγ'0 : γ' 0 = y := by
    change θc.symm (pathc 0) = y
    rw [hpath0]
    exact θc.left_inv hyθ
  have hQγ : ∀ s, (θ (γ' s), P.height (γ' s).1) = (θ y + σ s, P.height y.1) := fun s => by
    have h1 := hθQ (γ' s) (hγ'src s)
    have h2 : θc (γ' s) = pathc s := θc.right_inv (hmem s)
    rw [h2] at h1
    have h3 : (θc y).1 = (θ y, P.height y.1) := hθQ y hyθ
    change ((θc y).1.1 + σ s, (θc y).1.2) = _ at h1
    rw [h3] at h1
    exact h1.symm
  have hθγ : ∀ s, θ (γ' s) = θ y + σ s := fun s => congrArg Prod.fst (hQγ s)
  have hHγ : ∀ s, P.height (γ' s).1 = P.level := fun s =>
    (congrArg Prod.snd (hQγ s)).trans hlevel
  let γ : ℝ → TotalC_ECM hg := fun s => ofUnder_ECM hg (γ' s) (le_of_eq (hHγ s))
  have hγsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ := by
    rw [P.contMDiff_total_iff_ECM]
    exact (contMDiff_subtype_val (U := P.source)).comp
      ((contMDiff_subtype_val (U := underCircle_ECM hg)).comp hγ'sm)
  have hγ0 : γ 0 = x := by
    apply Subtype.ext
    change (γ' 0).1.1 = x.1
    rw [hγ'0]
    rfl
  refine ⟨γ, hγsm, hγ0, fun s => ?_, ?_⟩
  · rw [P.total_isBoundaryPoint_iff_ECM]
    exact (P.heightExt_apply_ECM (γ' s).1).trans (hHγ s)
  · have hφ : ∀ s, (totalProj_ECM hg ∘ γ) s = projCircle_ECM hg (γ' s) := fun s => rfl
    have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), Circle.exp (θ y + σ s) = projCircle_ECM hg (γ' s) := by
      have h := (hγ'sm.continuous.tendsto' 0 y hγ'0).eventually hev
      filter_upwards [h] with s hs
      rw [← hθγ s]
      exact hs
    have hpθ : (totalProj_ECM hg ∘ γ) =ᶠ[𝓝 (0 : ℝ)] fun s => Circle.exp (θ y + σ s) := by
      filter_upwards [hev'] with s hs
      rw [hφ s]
      exact hs.symm
    have hθ'd : HasDerivAt (fun s : ℝ => θ y + σ s) 1 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s / r) (1 / r) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).div_const r
      have h2 := ((Real.hasDerivAt_sin (0 / r)).comp (0 : ℝ) h1).const_mul r
      have h3 := h2.const_add (θ y)
      have h4 : r * (Real.cos (0 / r) * (1 / r)) = 1 := by
        simp [hr0.ne']
      rw [h4] at h3
      exact h3
    have hθ'md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => θ y + σ s) 0 :=
      hθ'd.differentiableAt.mdifferentiableAt
    have hrel := DifferentialGeometry.Manifold.BoundaryTangentFlow.mfderiv_apply_eq_of_local_angle
      hθ'md hpθ (1 : ℝ)
    have hone : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => θ y + σ s) 0 : ℝ →L[ℝ] ℝ) 1 = 1 := by
      rw [mfderiv_eq_fderiv, hθ'd.hasFDerivAt.fderiv]
      simp
      rfl
    intro h0
    apply mfderiv_exp_angle_ne_zero_ECM hg y hθ hev
    let E1 := EuclideanSpace ℝ (Fin 1)
    let F : ℝ → E1 := fun c => (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp c : ℝ →L[ℝ] E1) 1
    have h2 : ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (totalProj_ECM hg ∘ γ) 0 : ℝ →L[ℝ] E1) 1) =
        F (θ y + σ 0) :=
      hrel.trans (congrArg (fun t : ℝ =>
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp (θ y + σ 0) : ℝ →L[ℝ] E1) t) hone)
    have h3 : F (θ y + σ 0) = F (θ y) := congrArg F (by rw [hσ0, add_zero])
    have h4 : ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (totalProj_ECM hg ∘ γ) 0 : ℝ →L[ℝ] E1) 1) = 0 := by
      rw [h0]
      rfl
    exact (h3.symm.trans h2.symm).trans h4

end EdgeBundle

end GC.GraphManifold.Assembly.FC39P0
