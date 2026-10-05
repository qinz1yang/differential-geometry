import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutOrientCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar

/-!
# Chapter-14 assembly, L2 COMPARE A6-b, part 2: shell ball charts of the closed component models

Lane ASM-L2d. For the cut-and-capped data `X` of a sphere seam and a component decomposition `DQ`
of the capped carrier whose components have empty boundary:

* `SphereCutCapped.shellChart`, `shellBase`, `shellSlope`: a choice of the A6-a shell ball chart
  (`RelativeSphereCapping.exists_shellBallChart`) of each cut sphere `j : Fin 2`, with its facts;
* `cap_mem_spherePiece`, `shellChart_image_subset`: the cap and the shell chart of the cut sphere
  `j` lie in the component `spherePiece` of `j`;
* `componentModel`: the closed oriented model (B0) of a component;
* `componentBallChart`: the shell chart, restricted to the component of `0` of its source and
  corestricted to its component, as a ball chart of the closed model (`componentBallChart_val`:
  same values on the closed ball of radius `2`);
* `mem_chart_image_ball_iff`, `mem_chart_image_closedBall_iff`, `boundaryMap_val`,
  `radialMap_val`: for any ball chart `β` of the closed model with the values of the shell chart
  precomposed with a linear isometry, its punctured part, its interior, its boundary sphere and its
  radial collar, read in the capped carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The closed oriented model (B0) of a component with empty boundary. -/
abbrev componentModel (Q : CompactCarrier.{u}) (DQ : Q.Components)
    (hQ : ∀ i, (GC.Topology.componentCarrier Q DQ i).model.boundary
      (GC.Topology.componentCarrier Q DQ i).Carrier = ∅) (p : Fin DQ.count) :
    ConnectedClosedOrientedManifold.{u} 3 :=
  @boundaryEmptyClosedModel (GC.Topology.componentCarrier Q DQ p) (hQ p) (DQ.connected p)

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- A6-a for the cut sphere `j`. -/
theorem exists_shell (j : Fin 2) :
    ∃ (c : PartialDiffeomorph (𝓡 3) X.Q.model (EuclideanSpace ℝ (Fin 3)) X.Q.Carrier ∞)
      (s₀ μ : ℝ) (hs₀ : 0 < s₀) (hμ : 0 < μ), s₀ + μ < 1 ∧
      Metric.closedBall 0 2 ⊆ c.source ∧ c.target ⊆ X.Q.interior ∧
      (∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
        c (r • (z : EuclideanSpace ℝ (Fin 3))) =
          X.capping.core (X.B.sphere (Fin.cast X.h2.symm j) (ULift.up z,
            halfPoint (s₀ + μ * (r - 1))
              (add_nonneg hs₀.le (mul_nonneg hμ.le (sub_nonneg.mpr hr)))))) ∧
      c '' Metric.ball 0 1 =
        range (X.capping.cap (Fin.cast X.h2.symm j)) ∪
          X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm j) '' {p | p.2.val 0 < s₀}) :=
  RelativeSphereCapping.exists_shellBallChart X.capping (Fin.cast X.h2.symm j)

/-- The chosen shell ball chart (A6-a) of the cut sphere `j`. -/
def shellChart (j : Fin 2) :
    PartialDiffeomorph (𝓡 3) X.Q.model (EuclideanSpace ℝ (Fin 3)) X.Q.Carrier ∞ :=
  (X.exists_shell j).choose

/-- The base height of the shell of the chosen shell chart. -/
def shellBase (j : Fin 2) : ℝ := (X.exists_shell j).choose_spec.choose

/-- The height slope of the shell of the chosen shell chart. -/
def shellSlope (j : Fin 2) : ℝ := (X.exists_shell j).choose_spec.choose_spec.choose

theorem shellBase_pos (j : Fin 2) : 0 < X.shellBase j :=
  (X.exists_shell j).choose_spec.choose_spec.choose_spec.choose

theorem shellSlope_pos (j : Fin 2) : 0 < X.shellSlope j :=
  (X.exists_shell j).choose_spec.choose_spec.choose_spec.choose_spec.choose

theorem shellBase_add_slope_lt_one (j : Fin 2) : X.shellBase j + X.shellSlope j < 1 :=
  (X.exists_shell j).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1

theorem closedBall_subset_shellChart_source (j : Fin 2) :
    Metric.closedBall 0 2 ⊆ (X.shellChart j).source :=
  (X.exists_shell j).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1

theorem shellChart_target_subset (j : Fin 2) : (X.shellChart j).target ⊆ X.Q.interior :=
  (X.exists_shell j).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1

theorem shellChart_image_ball (j : Fin 2) :
    X.shellChart j '' Metric.ball 0 1 =
      range (X.capping.cap (Fin.cast X.h2.symm j)) ∪
        X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm j) '' {p | p.2.val 0 < X.shellBase j}) :=
  (X.exists_shell j).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2

/-- The shell of the chosen chart is the cut collar at heights `s₀ + μ (r - 1)`. -/
theorem shellChart_smul (j : Fin 2) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    X.shellChart j (r • (z : EuclideanSpace ℝ (Fin 3))) =
      X.capping.core (X.B.sphere (Fin.cast X.h2.symm j)
        (ULift.up z, halfSpaceOneLift (X.shellBase j + X.shellSlope j * (r - 1)))) := by
  have h := (X.exists_shell j).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
    z r hr hr2
  refine h.trans ?_
  congr 3
  exact halfPoint_eq_self _ _ (by
    rw [shellLift_coord, max_eq_left (add_nonneg (X.shellBase_pos j).le
      (mul_nonneg (X.shellSlope_pos j).le (sub_nonneg.mpr hr)))]
    rfl)

variable (DQ : X.Q.Components)

/-- The cap of the cut sphere `i` lies in its component. -/
theorem cap_mem_spherePiece (i : Fin X.B.sphereCount) (y : ClosedCell 3) :
    X.capping.cap i y ∈ DQ.piece (X.spherePiece DQ i) := by
  have := closureSphere_connectedSpace.{u}
  have := closedCell_three_connectedSpace
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  have h₀ : X.capping.cap i (closureSphereToBall z₀) ∈ DQ.piece (X.spherePiece DQ i) := by
    rw [X.capping.boundary_eq]
    exact X.sphere_mem_spherePiece DQ i _
  have hconn : IsConnected (range (X.capping.cap i)) := isConnected_range (X.capping.cap i).continuous
  exact hconn.isPreconnected.subset_isClopen (isClopen_componentsPiece DQ _)
    ⟨_, ⟨_, rfl⟩, h₀⟩ ⟨y, rfl⟩

/-- The shell chart of the cut sphere `j`, on the closed ball of radius `2`, lies in the component
of `j`. -/
theorem shellChart_image_subset (j : Fin 2) :
    X.shellChart j '' Metric.closedBall 0 2 ⊆
      DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) := by
  have := closedCell_three_connectedSpace
  obtain ⟨y⟩ := (inferInstance : Nonempty (ClosedCell 3))
  have hy : X.capping.cap (Fin.cast X.h2.symm j) y ∈ X.shellChart j '' Metric.ball 0 1 := by
    rw [X.shellChart_image_ball j]
    exact Or.inl ⟨y, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hy
  have hconn : IsPreconnected (X.shellChart j '' Metric.closedBall 0 2) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).isPreconnected.image _
      ((X.shellChart j).contMDiffOn.continuousOn.mono (X.closedBall_subset_shellChart_source j))
  refine hconn.subset_isClopen (isClopen_componentsPiece DQ _) ⟨X.shellChart j x, ⟨x, ?_, rfl⟩, ?_⟩
  · exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num)) hx
  · rw [hxe]
    exact X.cap_mem_spherePiece DQ _ y

/-- The component of `0` in the source of the shell chart. -/
def shellCore (j : Fin 2) : Set (EuclideanSpace ℝ (Fin 3)) :=
  connectedComponentIn (X.shellChart j).source 0

theorem isOpen_shellCore (j : Fin 2) : IsOpen (X.shellCore j) :=
  (X.shellChart j).open_source.connectedComponentIn

theorem shellCore_subset_source (j : Fin 2) : X.shellCore j ⊆ (X.shellChart j).source :=
  connectedComponentIn_subset _ _

theorem closedBall_subset_shellCore (j : Fin 2) : Metric.closedBall 0 2 ⊆ X.shellCore j :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).isPreconnected.subset_connectedComponentIn
    (Metric.mem_closedBall_self (by norm_num)) (X.closedBall_subset_shellChart_source j)

theorem shellChart_image_shellCore_subset (j : Fin 2) :
    X.shellChart j '' X.shellCore j ⊆ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) := by
  have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ Metric.closedBall 0 2 :=
    Metric.mem_closedBall_self (by norm_num)
  have hconn : IsPreconnected (X.shellChart j '' X.shellCore j) :=
    isPreconnected_connectedComponentIn.image _
      ((X.shellChart j).contMDiffOn.continuousOn.mono (X.shellCore_subset_source j))
  exact hconn.subset_isClopen (isClopen_componentsPiece DQ _)
    ⟨X.shellChart j 0, ⟨0, X.closedBall_subset_shellCore j h0, rfl⟩,
      X.shellChart_image_subset DQ j ⟨0, h0, rfl⟩⟩

/-- The shell chart restricted to the component of `0` of its source. -/
def shellChartCore (j : Fin 2) :
    PartialDiffeomorph (𝓡 3) X.Q.model (EuclideanSpace ℝ (Fin 3)) X.Q.Carrier ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict (X.shellChart j) (X.shellCore j)
    (X.isOpen_shellCore j)

theorem shellChartCore_source (j : Fin 2) : (X.shellChartCore j).source = X.shellCore j :=
  inter_eq_right.mpr (X.shellCore_subset_source j)

theorem shellChartCore_target_subset (j : Fin 2) :
    (X.shellChartCore j).target ⊆ (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) :
      Set X.Q.Carrier) := by
  intro y hy
  rw [← (X.shellChartCore j).right_inv hy]
  apply X.shellChart_image_shellCore_subset DQ j
  refine ⟨(X.shellChartCore j).symm y, ?_, rfl⟩
  have h := (X.shellChartCore j).map_target hy
  rw [X.shellChartCore_source] at h
  exact h


/-- The shell chart restricted to the component of `0` of its source, corestricted to the
component of the cut sphere `j`. -/
def componentShellChart (j : Fin 2) :
    PartialDiffeomorph (𝓡 3)
      (GC.Topology.componentCarrier X.Q DQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).model
      (EuclideanSpace ℝ (Fin 3))
      (GC.Topology.componentCarrier X.Q DQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier ∞ :=
  codRestrictOpens (X.shellChartCore j) (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)))
    ⟨⟨X.shellChart j 0, X.shellChart_image_subset DQ j
      ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩⟩⟩

theorem componentShellChart_source (j : Fin 2) :
    (X.componentShellChart DQ j).source = X.shellCore j := by
  rw [componentShellChart, codRestrictOpens_source _ _ _ (X.shellChartCore_target_subset DQ j),
    X.shellChartCore_source]

theorem componentShellChart_val (j : Fin 2) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ X.shellCore j) :
    (Subtype.val (X.componentShellChart DQ j x) : X.Q.Carrier) = X.shellChart j x := by
  refine codRestrictOpens_apply (I := 𝓡 3) (J := X.Q.model) _ _ _ ?_
  apply X.shellChartCore_target_subset DQ j
  apply (X.shellChartCore j).map_source
  rw [X.shellChartCore_source]
  exact hx

variable (hQ : ∀ i, (GC.Topology.componentCarrier X.Q DQ i).model.boundary
  (GC.Topology.componentCarrier X.Q DQ i).Carrier = ∅)

/-- **The shell ball chart of the closed model of the component of the cut sphere `j`.** -/
def componentBallChart (j : Fin 2) :
    BallChart 3 (𝓡 3)
      (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier where
  chart :=
    letI := boundaryEmptyChartedSpace (GC.Topology.componentCarrier X.Q DQ
      (X.spherePiece DQ (Fin.cast X.h2.symm j))) (hQ _)
    (X.componentShellChart DQ j).trans
      (boundaryEmptyDiffeomorph (GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm j))) (hQ _)).toPartialDiffeomorph
  closedBall_subset_source := by
    intro x hx
    refine ⟨?_, mem_univ _⟩
    change x ∈ (X.componentShellChart DQ j).source
    rw [X.componentShellChart_source]
    exact X.closedBall_subset_shellCore j hx

theorem componentBallChart_val (j : Fin 2) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Metric.closedBall 0 2) :
    (Subtype.val ((X.componentBallChart DQ hQ j).chart x) : X.Q.Carrier) = X.shellChart j x :=
  X.componentShellChart_val DQ j (X.closedBall_subset_shellCore j hx)

section Generic

variable {X DQ hQ} {j : Fin 2}
  {β : BallChart 3 (𝓡 3)
    (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier}
  {A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)}

theorem mem_isometry_ball_iff {r : ℝ} {x : EuclideanSpace ℝ (Fin 3)} :
    A x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r ↔ x ∈ Metric.ball 0 r := by
  simp only [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]

theorem mem_isometry_closedBall_iff {r : ℝ} {x : EuclideanSpace ℝ (Fin 3)} :
    A x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r ↔ x ∈ Metric.closedBall 0 r := by
  simp only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]

variable (hβ : ∀ x ∈ Metric.closedBall 0 2,
  (Subtype.val (β.chart x) : X.Q.Carrier) = X.shellChart j (A x))
include hβ

/-- A point of the closed model is in the open unit ball of `β` iff it is in that of the shell
chart. -/
theorem mem_chart_image_ball_iff_of_isometry {r : ℝ} (hr : r ≤ 2)
    {x : (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier} :
    x ∈ β.chart '' Metric.ball 0 r ↔
      (Subtype.val x : X.Q.Carrier) ∈ X.shellChart j '' Metric.ball 0 r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨A y, mem_isometry_ball_iff.mpr hy, ?_⟩
    rw [hβ y (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr) hy)]
  · rintro ⟨y, hy, he⟩
    refine ⟨A.symm y, (mem_isometry_ball_iff (A := A)).mp (by simpa using hy), ?_⟩
    apply Subtype.ext
    rw [hβ _ ((mem_isometry_closedBall_iff (A := A)).mp (by
      simpa using Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr) hy)),
      LinearIsometryEquiv.apply_symm_apply, he]

theorem mem_chart_image_closedBall_iff_of_isometry {r : ℝ} (hr : r ≤ 2)
    {x : (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier} :
    x ∈ β.chart '' Metric.closedBall 0 r ↔
      (Subtype.val x : X.Q.Carrier) ∈ X.shellChart j '' Metric.closedBall 0 r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨A y, mem_isometry_closedBall_iff.mpr hy, ?_⟩
    rw [hβ y (Metric.closedBall_subset_closedBall hr hy)]
  · rintro ⟨y, hy, he⟩
    refine ⟨A.symm y, (mem_isometry_closedBall_iff (A := A)).mp (by simpa using hy), ?_⟩
    apply Subtype.ext
    rw [hβ _ ((mem_isometry_closedBall_iff (A := A)).mp (by
      simpa using Metric.closedBall_subset_closedBall hr hy)),
      LinearIsometryEquiv.apply_symm_apply, he]

theorem boundaryMap_val_of_isometry (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (Subtype.val (β.boundaryMap z).val : X.Q.Carrier) =
      X.shellChart j (A (z : EuclideanSpace ℝ (Fin 3))) :=
  hβ z (Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num))
    z.property)

theorem radialMap_val_of_isometry (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (r : ℝ)
    (hr : r ∈ Icc (1 : ℝ) 2) :
    (Subtype.val (β.radialMap z r hr).val : X.Q.Carrier) =
      X.shellChart j (r • A (z : EuclideanSpace ℝ (Fin 3))) := by
  change (Subtype.val (β.chart (r • (z : EuclideanSpace ℝ (Fin 3)))) : X.Q.Carrier) = _
  rw [hβ _ (by
    rw [mem_closedBall_zero_iff, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2), map_smul]

end Generic

end SphereCutCapped

end GC.GraphManifold.Assembly
