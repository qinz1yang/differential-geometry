import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutOrientApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutFoldStretch

/-!
# Chapter-14 assembly, L2 COMPARE A6-c, part 2: the fold of a capped component onto `W`

Lane ASM-L2d. For the cut sphere `j` of `X : SphereCutCapped W S E` (no boundary tori) with its
shell chart `c = X.shellChart j` (A6-a), and a slope `0 < a ≤ μ_j`:

* `foldLift j a : X.Q → X.C`: on the shell `c (r z)`, `1 ≤ r ≤ 2`, the cut collar point at the
  stretched height `foldStretch a s₀ μ (r - 1)`; elsewhere the inverse of the core (`coreInv`);
* `foldMap j a := X.fold ∘ foldLift j a`: on the shell it is the seam collar
  `S.collar (z, ± foldStretch (r - 1))` (`foldMap_smul`), at the unit sphere the seam itself
  (`foldMap_unit`), off the ball of radius `3/2` it is `coreFold` (`foldMap_eq_coreFold`).

On the punctured component `{x ∈ piece | x ∉ c '' ball 0 1}`:
* `foldLift` is injective, onto the core preimage of the component, and hits height `0` exactly
  on the unit sphere of `c`;
* `foldMap` is injective, a local diffeomorphism off `c '' closedBall 0 1`, and the two sides meet
  exactly along the unit spheres (`foldMap_cross`) and cover `W` (`foldMap_cover`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The closed shell `1 ≤ ‖x‖ ≤ 2`. -/
def foldShell : Set (EuclideanSpace ℝ (Fin 3)) := {y | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 2}

/-- The sign of the side `j` of the seam. -/
def sideSign (j : Fin 2) : ℝ := if j.val = 0 then 1 else -1

theorem sideSign_ne_zero (j : Fin 2) : sideSign j ≠ 0 := by
  unfold sideSign
  split_ifs <;> norm_num

theorem sideSign_mul (j : Fin 2) (h : ℝ) : sideSign j * h = if j.val = 0 then h else -h := by
  unfold sideSign
  split_ifs <;> ring

theorem foldShell_subset_closedBall : foldShell ⊆ Metric.closedBall 0 2 := fun _ hy =>
  mem_closedBall_zero_iff.mpr hy.2

theorem smul_mem_foldShell (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ}
    (hr : 1 ≤ r) (hr2 : r ≤ 2) : r • (z : EuclideanSpace ℝ (Fin 3)) ∈ foldShell := by
  change 1 ≤ ‖r • (z : EuclideanSpace ℝ (Fin 3))‖ ∧ ‖r • (z : EuclideanSpace ℝ (Fin 3))‖ ≤ 2
  rw [norm_smul_sphere z (by linarith)]
  exact ⟨hr, hr2⟩

theorem shellPolar_of_ne {y : EuclideanSpace ℝ (Fin 3)} (hy : y ≠ 0) :
    shellPolar y = (shellDir hy, ‖y‖) := by
  have h := shellPolar_smul (shellDir hy) (norm_pos_iff.mpr hy)
  rwa [shellDir_smul] at h

theorem exists_smul_of_mem_foldShell {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ foldShell) :
    ∃ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (r : ℝ), 1 ≤ r ∧ r ≤ 2 ∧
      y = r • (z : EuclideanSpace ℝ (Fin 3)) := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le one_pos hy.1)
  exact ⟨shellDir hy0, ‖y‖, hy.1, hy.2, (shellDir_smul hy0).symm⟩

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {E : BoundaryTori W 0}
  (X : SphereCutCapped W S E)

/-- The inverse of the core (off the core: a fixed point). -/
def coreInv (x : X.Q.Carrier) : X.C.Carrier :=
  haveI := Classical.propDecidable
  if h : ∃ y, X.capping.core y = x then h.choose
  else X.B.sphere (Fin.cast X.h2.symm 0) (ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, halfZero)

theorem coreInv_core (y : X.C.Carrier) : X.coreInv (X.capping.core y) = y := by
  have h : ∃ y', X.capping.core y' = X.capping.core y := ⟨y, rfl⟩
  unfold coreInv
  rw [dite_eq_left h]
  exact core_injective X.capping h.choose_spec

theorem core_coreInv {x : X.Q.Carrier} (hx : x ∈ range X.capping.core) :
    X.capping.core (X.coreInv x) = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [coreInv_core]

theorem fold_coreInv (x : X.Q.Carrier) : X.fold (X.coreInv x) = X.coreFold x := by
  unfold coreInv coreFold
  split_ifs <;> rfl

theorem shellChart_symm_apply (j : Fin 2) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Metric.closedBall 0 2) : (X.shellChart j).symm (X.shellChart j y) = y :=
  (X.shellChart j).left_inv (X.closedBall_subset_shellChart_source j hy)

theorem shellChart_injOn (j : Fin 2) : InjOn (X.shellChart j) (Metric.closedBall 0 2) :=
  (X.shellChart j).injOn.mono (X.closedBall_subset_shellChart_source j)

/-- The lift of the fold: the stretched cut collar on the shell, the inverse of the core elsewhere. -/
def foldLift (j : Fin 2) (a : ℝ) (x : X.Q.Carrier) : X.C.Carrier :=
  haveI := Classical.propDecidable
  if x ∈ X.shellChart j '' foldShell then
    X.B.sphere (Fin.cast X.h2.symm j)
      (ULift.up (shellPolar ((X.shellChart j).symm x)).1,
        halfSpaceOneLift (foldStretch a (X.shellBase j) (X.shellSlope j)
          ((shellPolar ((X.shellChart j).symm x)).2 - 1)))
  else X.coreInv x

/-- **The fold of a capped component.** -/
def foldMap (j : Fin 2) (a : ℝ) (x : X.Q.Carrier) : W.Carrier := X.fold (X.foldLift j a x)

theorem foldLift_smul (j : Fin 2) (a : ℝ) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    X.foldLift j a (X.shellChart j (r • (z : EuclideanSpace ℝ (Fin 3)))) =
      X.B.sphere (Fin.cast X.h2.symm j) (ULift.up z,
        halfSpaceOneLift (foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1))) := by
  have hm : X.shellChart j (r • (z : EuclideanSpace ℝ (Fin 3))) ∈ X.shellChart j '' foldShell :=
    ⟨_, smul_mem_foldShell z hr hr2, rfl⟩
  unfold foldLift
  rw [ite_eq_left hm, X.shellChart_symm_apply j (foldShell_subset_closedBall
    (smul_mem_foldShell z hr hr2)), shellPolar_smul z (by linarith)]

theorem foldLift_of_notMem (j : Fin 2) (a : ℝ) {x : X.Q.Carrier}
    (hx : x ∉ X.shellChart j '' foldShell) : X.foldLift j a x = X.coreInv x := by
  unfold foldLift
  rw [ite_eq_right hx]

/-- The cut collar of the sphere `j` up to the top of the shell lies in the closed ball of radius
`2` of the shell chart: below `s₀` in the open unit ball, above in the shell. -/
theorem core_sphere_mem_shellChart (j : Fin 2) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ X.shellBase j + X.shellSlope j) :
    (h < X.shellBase j ∧ X.capping.core (X.B.sphere (Fin.cast X.h2.symm j)
        (ULift.up z, halfSpaceOneLift h)) ∈ X.shellChart j '' Metric.ball 0 1) ∨
      (X.shellBase j ≤ h ∧ X.capping.core (X.B.sphere (Fin.cast X.h2.symm j)
        (ULift.up z, halfSpaceOneLift h)) =
          X.shellChart j ((1 + (h - X.shellBase j) / X.shellSlope j) •
            (z : EuclideanSpace ℝ (Fin 3)))) := by
  have hμ := X.shellSlope_pos j
  rcases lt_or_ge h (X.shellBase j) with hlt | hge
  · refine Or.inl ⟨hlt, ?_⟩
    rw [X.shellChart_image_ball j]
    refine Or.inr ⟨_, ⟨(ULift.up z, halfSpaceOneLift h), ?_, rfl⟩, rfl⟩
    change (halfSpaceOneLift h).val 0 < X.shellBase j
    rw [shellLift_coord, max_eq_left h0]
    exact hlt
  · refine Or.inr ⟨hge, ?_⟩
    have hr1 : 1 ≤ 1 + (h - X.shellBase j) / X.shellSlope j := by
      have := div_nonneg (sub_nonneg.mpr hge) hμ.le
      linarith
    have hr2 : 1 + (h - X.shellBase j) / X.shellSlope j ≤ 2 := by
      have : (h - X.shellBase j) / X.shellSlope j ≤ 1 := by
        rw [div_le_one hμ]
        linarith
      linarith
    rw [X.shellChart_smul j z hr1 hr2]
    congr 4
    field_simp
    ring

theorem core_sphere_mem_closedBall (j : Fin 2) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ X.shellBase j + X.shellSlope j) :
    X.capping.core (X.B.sphere (Fin.cast X.h2.symm j) (ULift.up z, halfSpaceOneLift h)) ∈
      X.shellChart j '' Metric.closedBall 0 2 := by
  rcases X.core_sphere_mem_shellChart j z h0 h1 with ⟨-, ⟨y, hy, he⟩⟩ | ⟨hge, he⟩
  · exact ⟨y, Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      (by norm_num)) hy, he⟩
  · have hμ := X.shellSlope_pos j
    have hr1 : 1 ≤ 1 + (h - X.shellBase j) / X.shellSlope j := by
      have := div_nonneg (sub_nonneg.mpr hge) hμ.le
      linarith
    have hr2 : 1 + (h - X.shellBase j) / X.shellSlope j ≤ 2 := by
      have : (h - X.shellBase j) / X.shellSlope j ≤ 1 := by
        rw [div_le_one hμ]
        linarith
      linarith
    exact ⟨_, foldShell_subset_closedBall (smul_mem_foldShell z hr1 hr2), he.symm⟩

/-- The unit ball of the shell chart contains the cut sphere at height `0`. -/
theorem core_sphere_zero_mem_ball (j : Fin 2) (w : ClosureSphere.{u}) :
    X.capping.core (X.B.sphere (Fin.cast X.h2.symm j) (w, halfZero)) ∈
      X.shellChart j '' Metric.ball 0 1 := by
  rw [X.shellChart_image_ball j]
  refine Or.inr ⟨_, ⟨(w, halfZero), ?_, rfl⟩, rfl⟩
  change (0 : ℝ) < X.shellBase j
  exact X.shellBase_pos j

/-- A point of the cut carrier off the cut spheres is interior (no boundary tori). -/
theorem isInteriorPoint_of_ne_sphere {y : X.C.Carrier}
    (h : ∀ i w, y ≠ X.B.sphere i (w, halfZero)) : X.C.model.IsInteriorPoint y := by
  by_contra hy
  have hb : y ∈ X.C.model.boundary X.C.Carrier :=
    (X.C.model.isInteriorPoint_or_isBoundaryPoint y).resolve_left hy
  rw [X.B.boundary_eq] at hb
  rcases hb with ht | hs
  · obtain ⟨i, -⟩ := mem_iUnion.mp ht
    exact (Fin.cast X.hn i).elim0
  · obtain ⟨i, w, rfl⟩ := mem_iUnion.mp hs
    exact h i w rfl

/-- A collar point of the cut sphere `i` at positive height is interior. -/
theorem isInteriorPoint_sphere (i : Fin X.B.sphereCount) (w : ClosureSphere.{u})
    {h : EuclideanHalfSpace 1} (h0 : 0 < h.val 0) (h1 : h.val 0 < 1) :
    X.C.model.IsInteriorPoint (X.B.sphere i (w, h)) := by
  refine X.isInteriorPoint_of_ne_sphere fun i' w' he => ?_
  have hs : (w, h) ∈ (X.B.sphere i).source := by
    rw [X.B.sphere_source]
    exact h1
  have hs' : (w', halfZero) ∈ (X.B.sphere i').source := by
    rw [X.B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  by_cases hii : i = i'
  · subst hii
    have := congrArg (fun q : ClosureSphere.{u} × EuclideanHalfSpace 1 => q.2.val 0)
      ((X.B.sphere i).injOn hs hs' he)
    change h.val 0 = 0 at this
    linarith
  · have hm : X.B.sphere i (w, h) ∈ (X.B.sphere i').target := by
      rw [he]
      exact (X.B.sphere i').map_source hs'
    exact Set.disjoint_left.mp (X.B.sphere_disjoint hii) ((X.B.sphere i).map_source hs) hm

section Pieces

variable [ConnectedSpace W.Carrier] (DQ : X.Q.Components) (h2 : DQ.count = 2)
include h2

/-- With two components, distinct cut spheres lie in distinct components. -/
theorem spherePiece_injective : Injective (X.spherePiece DQ) := by
  have hb := (Fintype.bijective_iff_surjective_and_card (X.spherePiece DQ)).mpr
    ⟨X.spherePiece_surjective DQ, by simp [X.h2, h2]⟩
  exact hb.1

/-- A point of the component of `j` off the cap of `j` is in the core. -/
theorem mem_range_core_of_mem_spherePiece (j : Fin 2) {x : X.Q.Carrier}
    (hx : x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)))
    (hcap : x ∉ range (X.capping.cap (Fin.cast X.h2.symm j))) : x ∈ range X.capping.core := by
  rcases X.capping.every_point x with ⟨y, rfl⟩ | ⟨i, y, rfl⟩
  · exact ⟨y, rfl⟩
  · by_cases hi : i = Fin.cast X.h2.symm j
    · subst hi
      exact (hcap ⟨y, rfl⟩).elim
    · have hne : X.spherePiece DQ i ≠ X.spherePiece DQ (Fin.cast X.h2.symm j) :=
        fun he => hi (X.spherePiece_injective DQ h2 he)
      exact (Set.disjoint_left.mp (DQ.disjoint hne) (X.cap_mem_spherePiece DQ i y) hx).elim

end Pieces

theorem shellChart_mem_image_ball_iff (j : Fin 2) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Metric.closedBall 0 2) {r : ℝ} (hr : r ≤ 2) :
    X.shellChart j y ∈ X.shellChart j '' Metric.ball 0 r ↔ ‖y‖ < r := by
  constructor
  · rintro ⟨y', hy', he⟩
    rw [← X.shellChart_injOn j (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hr) hy') hy he]
    exact mem_ball_zero_iff.mp hy'
  · intro h
    exact ⟨y, mem_ball_zero_iff.mpr h, rfl⟩

theorem shellChart_mem_image_closedBall_iff (j : Fin 2) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Metric.closedBall 0 2) {r : ℝ} (hr : r ≤ 2) :
    X.shellChart j y ∈ X.shellChart j '' Metric.closedBall 0 r ↔ ‖y‖ ≤ r := by
  constructor
  · rintro ⟨y', hy', he⟩
    rw [← X.shellChart_injOn j (Metric.closedBall_subset_closedBall hr hy') hy he]
    exact mem_closedBall_zero_iff.mp hy'
  · intro h
    exact ⟨y, mem_closedBall_zero_iff.mpr h, rfl⟩

theorem range_cap_subset_shellChart_ball (j : Fin 2) :
    range (X.capping.cap (Fin.cast X.h2.symm j)) ⊆ X.shellChart j '' Metric.ball 0 1 := by
  rw [X.shellChart_image_ball j]
  exact subset_union_left

theorem sphere_mem_source (i : Fin X.B.sphereCount) (z : ClosureSphere.{u}) {h : ℝ} (h1 : h < 1) :
    (z, halfSpaceOneLift h) ∈ (X.B.sphere i).source := by
  rw [X.B.sphere_source]
  exact shellLift_mem_source z h1

section Fibres

variable (j : Fin 2) {a : ℝ} (ha : 0 < a) (haμ : a ≤ X.shellSlope j)

include ha haμ in
theorem foldStretch_bounds {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1) ∧
      foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1) ≤ X.shellBase j + X.shellSlope j :=
  ⟨foldStretch_nonneg ha haμ (X.shellBase_pos j) (by linarith),
    foldStretch_le ha haμ (X.shellBase_pos j) (by linarith) (by linarith)⟩

include ha haμ in
theorem foldStretch_lt_one {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1) < 1 :=
  lt_of_le_of_lt (X.foldStretch_bounds j ha haμ hr hr2).2 (X.shellBase_add_slope_lt_one j)

variable [ConnectedSpace W.Carrier] (DQ : X.Q.Components) (h2 : DQ.count = 2)

include h2 ha haμ in
/-- The lift of a point of the punctured component lies over the component. -/
theorem core_foldLift_mem {x : X.Q.Carrier}
    (hx : x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)))
    (hxb : x ∉ X.shellChart j '' Metric.ball 0 1) :
    X.capping.core (X.foldLift j a x) ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) := by
  by_cases hs : x ∈ X.shellChart j '' foldShell
  · obtain ⟨y, hy, rfl⟩ := hs
    obtain ⟨z, r, hr1, hr2, rfl⟩ := exists_smul_of_mem_foldShell hy
    rw [X.foldLift_smul j a z hr1 hr2]
    obtain ⟨h0, h1⟩ := X.foldStretch_bounds j ha haμ hr1 hr2
    exact X.shellChart_image_subset DQ j (X.core_sphere_mem_closedBall j z h0 h1)
  · rw [X.foldLift_of_notMem j a hs, X.core_coreInv (X.mem_range_core_of_mem_spherePiece DQ h2 j hx
      fun h => hxb (X.range_cap_subset_shellChart_ball j h))]
    exact hx

include h2 ha haμ in
/-- The lift is injective on the punctured component. -/
theorem foldLift_injOn :
    InjOn (X.foldLift j a) {x | x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) ∧
      x ∉ X.shellChart j '' Metric.ball 0 1} := by
  have hshell : ∀ x x', x ∈ X.shellChart j '' foldShell → x' ∉ X.shellChart j '' foldShell →
      x' ∈ range X.capping.core → x' ∉ X.shellChart j '' Metric.ball 0 1 →
      X.foldLift j a x ≠ X.foldLift j a x' := by
    rintro x x' ⟨y, hy, rfl⟩ hs' hcore' hb' he
    obtain ⟨z, r, hr1, hr2, rfl⟩ := exists_smul_of_mem_foldShell hy
    rw [X.foldLift_smul j a z hr1 hr2, X.foldLift_of_notMem j a hs'] at he
    have hx' := X.core_coreInv hcore'
    rw [← he] at hx'
    obtain ⟨h0, h1⟩ := X.foldStretch_bounds j ha haμ hr1 hr2
    rcases X.core_sphere_mem_shellChart j z h0 h1 with ⟨-, hb⟩ | ⟨hge, hc⟩
    · rw [hx'] at hb
      exact hb' hb
    · apply hs'
      rw [← hx', hc]
      have hμ := X.shellSlope_pos j
      have hr1' : 1 ≤ 1 + (foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1) -
          X.shellBase j) / X.shellSlope j := by
        have := div_nonneg (sub_nonneg.mpr hge) hμ.le
        linarith
      have hr2' : 1 + (foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1) -
          X.shellBase j) / X.shellSlope j ≤ 2 := by
        have : (foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1) - X.shellBase j) /
            X.shellSlope j ≤ 1 := by
          rw [div_le_one hμ]
          linarith
        linarith
      exact ⟨_, smul_mem_foldShell z hr1' hr2', rfl⟩
  intro x hx x' hx' he
  have hcore : ∀ {x}, x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) →
      x ∉ X.shellChart j '' Metric.ball 0 1 → x ∈ range X.capping.core := fun hx hxb =>
    X.mem_range_core_of_mem_spherePiece DQ h2 j hx
      fun h => hxb (X.range_cap_subset_shellChart_ball j h)
  by_cases hs : x ∈ X.shellChart j '' foldShell <;> by_cases hs' : x' ∈ X.shellChart j '' foldShell
  · obtain ⟨y, hy, rfl⟩ := hs
    obtain ⟨y', hy', rfl⟩ := hs'
    obtain ⟨z, r, hr1, hr2, rfl⟩ := exists_smul_of_mem_foldShell hy
    obtain ⟨z', r', hr1', hr2', rfl⟩ := exists_smul_of_mem_foldShell hy'
    rw [X.foldLift_smul j a z hr1 hr2, X.foldLift_smul j a z' hr1' hr2'] at he
    have he' := (X.B.sphere (Fin.cast X.h2.symm j)).injOn
      (X.sphere_mem_source _ _ (X.foldStretch_lt_one j ha haμ hr1 hr2))
      (X.sphere_mem_source _ _ (X.foldStretch_lt_one j ha haμ hr1' hr2')) he
    have hz : z = z' := ULift.up_injective (congrArg Prod.fst he')
    have hh := congrArg (fun q : ClosureSphere.{u} × EuclideanHalfSpace 1 => q.2.val 0) he'
    simp only [shellLift_coord] at hh
    rw [max_eq_left (X.foldStretch_bounds j ha haμ hr1 hr2).1,
      max_eq_left (X.foldStretch_bounds j ha haμ hr1' hr2').1] at hh
    have hrr := foldStretch_injOn ha haμ (X.shellBase_pos j) (mem_Ici.mpr (by linarith))
      (mem_Ici.mpr (by linarith)) hh
    have hrr' : r = r' := by linarith
    rw [hz, hrr']
  · exact (hshell _ _ hs hs' (hcore hx'.1 hx'.2) hx'.2 he).elim
  · exact (hshell _ _ hs' hs (hcore hx.1 hx.2) hx.2 he.symm).elim
  · rw [X.foldLift_of_notMem j a hs, X.foldLift_of_notMem j a hs'] at he
    rw [← X.core_coreInv (hcore hx.1 hx.2), ← X.core_coreInv (hcore hx'.1 hx'.2), he]

omit [ConnectedSpace W.Carrier] in
include ha haμ in
/-- The lift is onto the core preimage of the component. -/
theorem exists_foldLift_eq {y : X.C.Carrier}
    (hy : X.capping.core y ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j))) :
    ∃ x, (x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) ∧
      x ∉ X.shellChart j '' Metric.ball 0 1) ∧ X.foldLift j a x = y := by
  by_cases hc : ∃ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (h : ℝ),
      0 ≤ h ∧ h ≤ X.shellBase j + X.shellSlope j ∧
        y = X.B.sphere (Fin.cast X.h2.symm j) (ULift.up z, halfSpaceOneLift h)
  · obtain ⟨z, h, h0, h1, rfl⟩ := hc
    obtain ⟨t, ⟨ht0, ht1⟩, hκ⟩ := exists_foldStretch_eq (a := a) h0 h1
    have hr1 : 1 ≤ 1 + t := by linarith
    have hr2 : 1 + t ≤ 2 := by linarith
    have hmem := smul_mem_foldShell z hr1 hr2
    refine ⟨X.shellChart j ((1 + t) • (z : EuclideanSpace ℝ (Fin 3))), ⟨?_, ?_⟩, ?_⟩
    · exact X.shellChart_image_subset DQ j ⟨_, foldShell_subset_closedBall hmem, rfl⟩
    · rw [X.shellChart_mem_image_ball_iff j (foldShell_subset_closedBall hmem) (by norm_num)]
      exact not_lt.mpr hmem.1
    · rw [X.foldLift_smul j a z hr1 hr2, show 1 + t - 1 = t by ring, hκ]
  · refine ⟨X.capping.core y, ⟨hy, ?_⟩, ?_⟩
    · intro hb
      rw [X.shellChart_image_ball j] at hb
      rcases hb with ⟨w, hw⟩ | ⟨c', ⟨q, hq, rfl⟩, he⟩
      · obtain ⟨z', rfl⟩ := exists_sphere_of_core_eq_cap X.capping hw.symm
        refine hc ⟨z'.down, 0, le_rfl, (add_pos (X.shellBase_pos j) (X.shellSlope_pos j)).le, ?_⟩
        rw [shellLift_zero]
      · have hq' := core_injective X.capping he
        subst hq'
        refine hc ⟨q.1.down, q.2.val 0, q.2.property, ?_, ?_⟩
        · have := X.shellSlope_pos j
          change q.2.val 0 < X.shellBase j at hq
          linarith
        · rw [shellLift_val]
    · have hs : X.capping.core y ∉ X.shellChart j '' foldShell := by
        rintro ⟨y', hy', he⟩
        obtain ⟨z, r, hr1, hr2, rfl⟩ := exists_smul_of_mem_foldShell hy'
        rw [X.shellChart_smul j z hr1 hr2] at he
        have he' := core_injective X.capping he
        refine hc ⟨z, X.shellBase j + X.shellSlope j * (r - 1),
          add_nonneg (X.shellBase_pos j).le (mul_nonneg (X.shellSlope_pos j).le (by linarith)),
          ?_, he'.symm⟩
        have := X.shellSlope_pos j
        nlinarith
      rw [X.foldLift_of_notMem j a hs, X.coreInv_core]

include h2 ha haμ in
/-- The lift of a point of the punctured component reaches height `0` only on the unit sphere of
the shell chart. -/
theorem foldLift_eq_sphere_zero {x : X.Q.Carrier}
    (hx : x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)))
    (hxb : x ∉ X.shellChart j '' Metric.ball 0 1) {w : ClosureSphere.{u}}
    (he : X.foldLift j a x = X.B.sphere (Fin.cast X.h2.symm j) (w, halfZero)) :
    x = X.shellChart j (w.down : EuclideanSpace ℝ (Fin 3)) := by
  by_cases hs : x ∈ X.shellChart j '' foldShell
  · obtain ⟨y, hy, rfl⟩ := hs
    obtain ⟨z, r, hr1, hr2, rfl⟩ := exists_smul_of_mem_foldShell hy
    rw [X.foldLift_smul j a z hr1 hr2] at he
    have hw0 : (w, halfZero) ∈ (X.B.sphere (Fin.cast X.h2.symm j)).source := by
      rw [X.B.sphere_source]
      change (0 : ℝ) < 1
      norm_num
    have he' := (X.B.sphere (Fin.cast X.h2.symm j)).injOn
      (X.sphere_mem_source _ _ (X.foldStretch_lt_one j ha haμ hr1 hr2)) hw0 he
    have hz : ULift.up z = w := congrArg Prod.fst he'
    have hh := congrArg (fun q : ClosureSphere.{u} × EuclideanHalfSpace 1 => q.2.val 0) he'
    simp only [shellLift_coord] at hh
    rw [max_eq_left (X.foldStretch_bounds j ha haμ hr1 hr2).1] at hh
    have h0 : foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1) =
        foldStretch a (X.shellBase j) (X.shellSlope j) 0 := by
      rw [foldStretch_zero]
      exact hh
    have hr : r - 1 = 0 := foldStretch_injOn ha haμ (X.shellBase_pos j)
      (mem_Ici.mpr (by linarith)) (mem_Ici.mpr le_rfl) h0
    rw [show r = 1 by linarith, one_smul, ← hz]
  · rw [X.foldLift_of_notMem j a hs] at he
    have hcore := X.mem_range_core_of_mem_spherePiece DQ h2 j hx
      fun h => hxb (X.range_cap_subset_shellChart_ball j h)
    have hx' := X.core_coreInv hcore
    rw [he] at hx'
    exact (hxb (hx' ▸ X.core_sphere_zero_mem_ball j w)).elim

omit [ConnectedSpace W.Carrier] in
include ha haμ in
/-- On the shell, the fold is the seam collar at the stretched signed height. -/
theorem foldMap_smul (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ} (hr : 1 ≤ r)
    (hr2 : r ≤ 2) :
    X.foldMap j a (X.shellChart j (r • (z : EuclideanSpace ℝ (Fin 3)))) =
      S.collar (ULift.up z, sideSign j * foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1)) := by
  obtain ⟨h0, -⟩ := X.foldStretch_bounds j ha haμ hr hr2
  have h1 := X.foldStretch_lt_one j ha haμ hr hr2
  unfold foldMap
  rw [X.foldLift_smul j a z hr hr2, sideSign_mul,
    ← halfPoint_eq_self (halfSpaceOneLift _) h0 (by rw [shellLift_coord, max_eq_left h0])]
  exact X.spheres j (ULift.up z) _ h0 h1

omit [ConnectedSpace W.Carrier] in
include ha haμ in
/-- On the unit sphere, the fold is the seam. -/
theorem foldMap_unit (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    X.foldMap j a (X.shellChart j (z : EuclideanSpace ℝ (Fin 3))) = S.collar (ULift.up z, 0) := by
  have h := X.foldMap_smul j ha haμ z le_rfl one_le_two
  rw [one_smul, sub_self, foldStretch_zero, mul_zero] at h
  exact h

omit [ConnectedSpace W.Carrier] in
/-- Off the ball of radius `3/2`, the fold is `coreFold`. -/
theorem foldMap_eq_coreFold {x : X.Q.Carrier}
    (hx : x ∉ X.shellChart j '' Metric.closedBall 0 (3 / 2)) : X.foldMap j a x = X.coreFold x := by
  by_cases hs : x ∈ X.shellChart j '' foldShell
  · obtain ⟨y, hy, rfl⟩ := hs
    obtain ⟨z, r, hr1, hr2, rfl⟩ := exists_smul_of_mem_foldShell hy
    have hr : 3 / 2 < r := by
      by_contra h
      exact hx ⟨_, by rw [mem_closedBall_zero_iff, norm_smul_sphere z (by linarith)]; linarith, rfl⟩
    unfold foldMap
    rw [X.foldLift_smul j a z hr1 hr2, foldStretch_of_ge a _ _ (by linarith),
      X.shellChart_smul j z hr1 hr2, X.coreFold_core]
  · unfold foldMap
    rw [X.foldLift_of_notMem j a hs, X.fold_coreInv]

omit [ConnectedSpace W.Carrier] in
/-- The cut sphere `i` at height `0` lies only in its own component. -/
theorem spherePiece_eq_of_mem {i : Fin X.B.sphereCount} {w : ClosureSphere.{u}}
    {k : Fin DQ.count} (h : X.capping.core (X.B.sphere i (w, halfZero)) ∈ DQ.piece k) :
    X.spherePiece DQ i = k := by
  by_contra hne
  exact Set.disjoint_left.mp (DQ.disjoint hne) (X.sphere_mem_spherePiece DQ i w) h

include h2 in
theorem spherePiece_ne : X.spherePiece DQ (Fin.cast X.h2.symm 0) ≠
    X.spherePiece DQ (Fin.cast X.h2.symm 1) := by
  intro he
  have := congrArg Fin.val (X.spherePiece_injective DQ h2 he)
  simp at this

include h2 ha haμ in
/-- The fold is injective on the punctured component. -/
theorem foldMap_injOn :
    InjOn (X.foldMap j a) {x | x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) ∧
      x ∉ X.shellChart j '' Metric.ball 0 1} := by
  intro x hx x' hx' he
  rcases X.fold_eq he with he' | ⟨w, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩
  · exact X.foldLift_injOn j ha haμ DQ h2 hx hx' he'
  · have k0 := X.spherePiece_eq_of_mem DQ (h0 ▸ X.core_foldLift_mem j ha haμ DQ h2 hx.1 hx.2)
    have k1 := X.spherePiece_eq_of_mem DQ (h1 ▸ X.core_foldLift_mem j ha haμ DQ h2 hx'.1 hx'.2)
    exact (X.spherePiece_ne DQ h2 (k0.trans k1.symm)).elim
  · have k0 := X.spherePiece_eq_of_mem DQ (h0 ▸ X.core_foldLift_mem j ha haμ DQ h2 hx'.1 hx'.2)
    have k1 := X.spherePiece_eq_of_mem DQ (h1 ▸ X.core_foldLift_mem j ha haμ DQ h2 hx.1 hx.2)
    exact (X.spherePiece_ne DQ h2 (k0.trans k1.symm)).elim

include h2 in
/-- A core point of the component of `j` off the closed unit ball of the shell chart comes from an
interior point of the cut carrier. -/
theorem isInteriorPoint_of_core_mem {y : X.C.Carrier}
    (hy : X.capping.core y ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)))
    (hyb : X.capping.core y ∉ X.shellChart j '' Metric.ball 0 1) :
    X.C.model.IsInteriorPoint y := by
  refine X.isInteriorPoint_of_ne_sphere fun i w he => ?_
  subst he
  by_cases hi : i = Fin.cast X.h2.symm j
  · subst hi
    exact hyb (X.core_sphere_zero_mem_ball j w)
  · exact hi (X.spherePiece_injective DQ h2 (X.spherePiece_eq_of_mem DQ hy))

include h2 ha haμ in
/-- **The fold is a local diffeomorphism off the closed unit ball of the shell chart.** -/
theorem isLocalDiffeomorphAt_foldMap {x : X.Q.Carrier}
    (hx : x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)))
    (hxb : x ∉ X.shellChart j '' Metric.closedBall 0 1) :
    IsLocalDiffeomorphAt X.Q.model W.model ∞ (X.foldMap j a) x := by
  by_cases h2b : x ∈ X.shellChart j '' Metric.ball 0 2
  · obtain ⟨y, hy, rfl⟩ := h2b
    have hy1 : 1 < ‖y‖ := by
      by_contra h
      exact hxb ⟨y, mem_closedBall_zero_iff.mpr (not_lt.mp h), rfl⟩
    have hy2 : ‖y‖ < 2 := mem_ball_zero_iff.mp hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
    have hyB : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 :=
      Metric.ball_subset_closedBall hy
    let T : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → ClosureSphere.{u} × ℝ :=
      Prod.map ULift.up (fun r => sideSign j * foldStretch a (X.shellBase j) (X.shellSlope j) (r - 1))
    let Φ : X.Q.Carrier → W.Carrier := fun x' => S.collar (T (shellPolar ((X.shellChart j).symm x')))
    have hcy : X.shellChart j y ∈ (X.shellChart j).target :=
      (X.shellChart j).map_source (X.closedBall_subset_shellChart_source j hyB)
    have h1 := (X.shellChart j).symm.isLocalDiffeomorphAt X.Q.model (𝓡 3) ∞ hcy
    have hsy : (X.shellChart j).symm (X.shellChart j y) = y := X.shellChart_symm_apply j hyB
    have h2' : IsLocalDiffeomorphAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ shellPolar
        ((X.shellChart j).symm (X.shellChart j y)) := by
      rw [hsy]
      exact shellPolar.isLocalDiffeomorphAt _ _ ∞ (mem_shellPolar_source hy0)
    have hpol : shellPolar ((X.shellChart j).symm (X.shellChart j y)) = (shellDir hy0, ‖y‖) := by
      rw [hsy, shellPolar_of_ne hy0]
    have h3 : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereSignedCollarModel ∞ T
        (shellPolar ((X.shellChart j).symm (X.shellChart j y))) := by
      rw [hpol]
      exact ((uliftDiffeomorph (I := 𝓡 2)
        (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).isLocalDiffeomorph _).prodMap
          (isLocalDiffeomorphAt_signedFoldStretch ha haμ (X.shellBase_pos j) (sideSign_ne_zero j)
            hy1.le)
    have hsrc : T (shellPolar ((X.shellChart j).symm (X.shellChart j y))) ∈ S.collar.source := by
      rw [hpol, S.source_eq]
      refine ⟨mem_univ _, ?_⟩
      have hb := X.foldStretch_bounds j ha haμ hy1.le hy2.le
      have hl := X.foldStretch_lt_one j ha haμ hy1.le hy2.le
      change sideSign j * foldStretch a (X.shellBase j) (X.shellSlope j) (‖y‖ - 1) ∈ Ioo (-1) 1
      unfold sideSign
      split_ifs <;> constructor <;> linarith
    have h4 := S.collar.isLocalDiffeomorphAt sphereSignedCollarModel W.model ∞ hsrc
    have hΦ : IsLocalDiffeomorphAt X.Q.model W.model ∞ Φ (X.shellChart j y) :=
      ((h1.comp _ _ h2').comp _ _ h3).comp _ _ h4
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ hΦ
    have hUo : IsOpen (X.shellChart j '' (Metric.ball 0 2 ∩ (Metric.closedBall 0 1)ᶜ)) :=
      (X.shellChart j).toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl)
        (fun y' hy' => X.closedBall_subset_shellChart_source j
          (Metric.ball_subset_closedBall hy'.1))
    have hyU : X.shellChart j y ∈ X.shellChart j '' (Metric.ball 0 2 ∩ (Metric.closedBall 0 1)ᶜ) :=
      ⟨y, ⟨hy, fun h => by linarith [mem_closedBall_zero_iff.mp h]⟩, rfl⟩
    filter_upwards [hUo.mem_nhds hyU]
    rintro _ ⟨y', ⟨hy'2, hy'1⟩, rfl⟩
    have h1' : 1 ≤ ‖y'‖ := by
      by_contra h
      exact hy'1 (mem_closedBall_zero_iff.mpr (not_le.mp h).le)
    have hy'0 : y' ≠ 0 := norm_pos_iff.mp (by linarith)
    have hy'B : y' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 :=
      Metric.ball_subset_closedBall hy'2
    obtain ⟨z, r, hr1, hr2, hzr⟩ := exists_smul_of_mem_foldShell
      ⟨h1', (mem_ball_zero_iff.mp hy'2).le⟩
    change X.foldMap j a (X.shellChart j y') = S.collar (T (shellPolar ((X.shellChart j).symm
      (X.shellChart j y'))))
    rw [X.shellChart_symm_apply j hy'B, hzr, X.foldMap_smul j ha haμ z hr1 hr2,
      shellPolar_smul z (by linarith)]
    rfl
  · have hx32 : x ∉ X.shellChart j '' Metric.closedBall 0 (3 / 2) := fun h =>
      h2b (image_mono (Metric.closedBall_subset_ball (by norm_num)) h)
    obtain ⟨y, rfl⟩ := X.mem_range_core_of_mem_spherePiece DQ h2 j hx fun h =>
      hxb (image_mono Metric.ball_subset_closedBall (X.range_cap_subset_shellChart_ball j h))
    have hint := X.isInteriorPoint_of_core_mem j DQ h2 hx
      fun h => hxb (image_mono Metric.ball_subset_closedBall h)
    have hcpt : IsCompact (X.shellChart j '' Metric.closedBall 0 (3 / 2)) :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 2)).image_of_continuousOn
        ((X.shellChart j).contMDiffOn.continuousOn.mono
          ((Metric.closedBall_subset_closedBall (by norm_num)).trans
            (X.closedBall_subset_shellChart_source j)))
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (X.isLocalDiffeomorphAt_coreFold hint)
    filter_upwards [hcpt.isClosed.isOpen_compl.mem_nhds hx32] with x' hx'
    exact X.foldMap_eq_coreFold j hx'

omit [ConnectedSpace W.Carrier] in
/-- A point of the component of `j` outside the ball of radius `3/2` of the shell chart, the core
image of an interior point (the top of the shell). -/
theorem exists_coreFold_point :
    ∃ x, x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) ∧
      x ∉ X.shellChart j '' Metric.closedBall 0 (3 / 2) ∧
      ∃ y, X.capping.core y = x ∧ X.C.model.IsInteriorPoint y := by
  let z₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hmem := smul_mem_foldShell z₀ one_le_two le_rfl
  have hB := foldShell_subset_closedBall hmem
  refine ⟨X.shellChart j ((2 : ℝ) • (z₀ : EuclideanSpace ℝ (Fin 3))),
    X.shellChart_image_subset DQ j ⟨_, hB, rfl⟩, ?_, ?_⟩
  · rw [X.shellChart_mem_image_closedBall_iff j hB (by norm_num), norm_smul_sphere z₀ (by norm_num)]
    norm_num
  · refine ⟨_, (X.shellChart_smul j z₀ one_le_two le_rfl).symm, ?_⟩
    have hs := X.shellBase_pos j
    have hμ := X.shellSlope_pos j
    have h1 := X.shellBase_add_slope_lt_one j
    apply X.isInteriorPoint_sphere
    · rw [shellLift_coord, max_eq_left (by nlinarith)]
      nlinarith
    · rw [shellLift_coord, max_eq_left (by nlinarith)]
      nlinarith

end Fibres

section TwoSides

variable [ConnectedSpace W.Carrier] (DQ : X.Q.Components) (h2 : DQ.count = 2) {a : ℝ} (ha : 0 < a)
  (ha0 : a ≤ X.shellSlope 0) (ha1 : a ≤ X.shellSlope 1)

include h2 ha ha0 ha1 in
variable {X} in
/-- **The two sides meet exactly along the unit spheres.** -/
theorem foldMap_cross {x x' : X.Q.Carrier}
    (hx : x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 0)))
    (hxb : x ∉ X.shellChart 0 '' Metric.ball 0 1)
    (hx' : x' ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 1)))
    (hxb' : x' ∉ X.shellChart 1 '' Metric.ball 0 1) :
    X.foldMap 0 a x = X.foldMap 1 a x' ↔ ∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      x = X.shellChart 0 (z : EuclideanSpace ℝ (Fin 3)) ∧
        x' = X.shellChart 1 (z : EuclideanSpace ℝ (Fin 3)) := by
  constructor
  · intro he
    rcases X.fold_eq he with he' | ⟨w, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩
    · have m0 := X.core_foldLift_mem 0 ha ha0 DQ h2 hx hxb
      have m1 := X.core_foldLift_mem 1 ha ha1 DQ h2 hx' hxb'
      rw [he'] at m0
      exact (Set.disjoint_left.mp (DQ.disjoint (X.spherePiece_ne DQ h2).symm) m1 m0).elim
    · exact ⟨w.down, X.foldLift_eq_sphere_zero 0 ha ha0 DQ h2 hx hxb h0,
        X.foldLift_eq_sphere_zero 1 ha ha1 DQ h2 hx' hxb' h1⟩
    · have k := X.spherePiece_eq_of_mem DQ (h1 ▸ X.core_foldLift_mem 0 ha ha0 DQ h2 hx hxb)
      exact (X.spherePiece_ne DQ h2 k.symm).elim
  · rintro ⟨z, rfl, rfl⟩
    rw [X.foldMap_unit 0 ha ha0 z, X.foldMap_unit 1 ha ha1 z]

include ha ha0 ha1 in
/-- **The two sides cover `W`.** -/
theorem foldMap_cover (w : W.Carrier) :
    (∃ x, (x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 0)) ∧
      x ∉ X.shellChart 0 '' Metric.ball 0 1) ∧ X.foldMap 0 a x = w) ∨
    (∃ x, (x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 1)) ∧
      x ∉ X.shellChart 1 '' Metric.ball 0 1) ∧ X.foldMap 1 a x = w) := by
  obtain ⟨y, rfl⟩ := X.surjective w
  obtain ⟨k, hk⟩ := exists_mem_componentsPiece DQ (X.capping.core y)
  obtain ⟨i, rfl⟩ := X.spherePiece_surjective DQ k
  have hlt : i.val < 2 := by
    have := i.isLt
    have := X.h2
    omega
  rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
  · have hi : i = Fin.cast X.h2.symm 0 := Fin.ext h
    subst hi
    obtain ⟨x, hx, he⟩ := X.exists_foldLift_eq 0 ha ha0 DQ hk
    exact Or.inl ⟨x, hx, by rw [foldMap, he]⟩
  · have hi : i = Fin.cast X.h2.symm 1 := Fin.ext h
    subst hi
    obtain ⟨x, hx, he⟩ := X.exists_foldLift_eq 1 ha ha1 DQ hk
    exact Or.inr ⟨x, hx, by rw [foldMap, he]⟩

end TwoSides

end SphereCutCapped

end GC.GraphManifold.Assembly
