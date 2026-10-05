import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutShellCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutBallChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelBallFill
import DifferentialGeometry.Geometry.Metric.PolarCoordinates
import DifferentialGeometry.Geometry.Collapse.CutPieceBalls
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.ULift

/-!
# Chapter-14 assembly, L2-relative COMPARE A6-a: the shell ball chart of a capped sphere

Lane ASM-L2c. For a relative sphere capping `K` and a cut sphere `i`, the cap together with the
cut collar below a height `s₀` is the image of the open unit ball under an interior ball chart of
the capped carrier whose shell `1 ≤ ‖x‖ ≤ 2` IS the cut collar at heights `s₀ + μ (‖x‖ - 1)`
(`RelativeSphereCapping.exists_shellBallChart`).

Route: the cap extends to a ball chart `φ` (`exists_ballChart_of_closedCell_interior`); the collar
near the cap lies in the target of `φ` (tube lemma); in the coordinates of `φ` the collar at heights
`s₀ + μ (‖x‖ - 1)` is a partial diffeomorphism `F` of `ℝ³` near the unit sphere (inverse function
theorem on the polar chart, the collar and the core); the smooth Schoenflies ball fill
`exists_ballFill_of_shell` gives a diffeomorphism `G` of `ℝ³` with `G = F` near the unit sphere and
`G '' ball 0 1` the cap region; `G` inside and `F` outside glue to the chart.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The sphere dimension instance used by the polar chart. -/
local instance shellDim_ASML2c : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The affine height `t ↦ a + b (t - 1)`. -/
def shellAffine (a b : ℝ) (hb : 0 < b) : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun t := a + b * (t - 1)
  invFun t := (t - a) / b + 1
  left_inv t := by field_simp; ring
  right_inv t := by field_simp; ring
  contMDiff_toFun :=
    (contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))).contMDiff
  contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const b |>.add contDiff_const).contMDiff

theorem shellAffine_apply (a b : ℝ) (hb : 0 < b) (t : ℝ) :
    shellAffine a b hb t = a + b * (t - 1) := rfl

/-- The polar chart `x ↦ (x / ‖x‖, ‖x‖)`. -/
def shellPolar : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (EuclideanSpace ℝ (Fin 3)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ∞ :=
  (DifferentialGeometry.Geometry.Riemannian.euclideanPolarDiffeomorph (n := 2)).symm

theorem shellPolar_smul (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ}
    (hr : 0 < r) : shellPolar (r • (z : EuclideanSpace ℝ (Fin 3))) = (z, r) := by
  have h := (DifferentialGeometry.Geometry.Riemannian.euclideanPolarDiffeomorph
    (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).left_inv (x := (z, r)) hr
  exact h

theorem mem_shellPolar_source {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    x ∈ shellPolar.source := hx

/-- `(z, t) ↦ (z, t)` into the cut-collar model, on positive heights. -/
def shellLiftPD : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereHalfCollarModel
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    (ClosureSphere.{u} × EuclideanHalfSpace 1) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.prod
    (uliftDiffeomorph (I := 𝓡 2)
      (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).toPartialDiffeomorph
    halfSpaceOneInteriorDiffeomorph

variable {C Q : CompactCarrier.{u}} {B : MixedBoundaryCertificate C}
  (K : RelativeSphereCapping C Q B) (i : Fin B.sphereCount)

/-- The cut collar of sphere `i` at height `a + b (‖x‖ - 1)` in direction `x / ‖x‖`. -/
def shellPD (a b : ℝ) (hb : 0 < b) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) C.model
      (EuclideanSpace ℝ (Fin 3)) C.Carrier ∞ :=
  shellPolar.trans ((((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    ∞).prodCongr (shellAffine a b hb)).toPartialDiffeomorph).trans
      (shellLiftPD.{u}.trans (B.sphere i)))

theorem shellPD_smul (a b : ℝ) (hb : 0 < b) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {r : ℝ} (hr : 0 < r) :
    shellPD i a b hb (r • (z : EuclideanSpace ℝ (Fin 3))) =
      B.sphere i (ULift.up z, halfSpaceOneLift (a + b * (r - 1))) := by
  change B.sphere i (shellLiftPD (((Diffeomorph.refl (𝓡 2)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr (shellAffine a b hb))
      (shellPolar (r • (z : EuclideanSpace ℝ (Fin 3)))))) = _
  rw [shellPolar_smul z hr]
  rfl

theorem mem_shellPD_source (a b : ℝ) (hb : 0 < b) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {r : ℝ} (hr : 0 < r) (h0 : 0 < a + b * (r - 1)) (h1 : a + b * (r - 1) < 1) :
    r • (z : EuclideanSpace ℝ (Fin 3)) ∈ (shellPD i a b hb).source := by
  have hx : r • (z : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    have hz : (z : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
      intro h
      have := norm_eq_of_mem_sphere z
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact smul_ne_zero hr.ne' hz
  refine ⟨mem_shellPolar_source hx, ?_⟩
  rw [Set.mem_preimage]
  have hp : shellPolar.toOpenPartialHomeomorph.symm.symm (r • (z : EuclideanSpace ℝ (Fin 3))) =
      (z, r) := shellPolar_smul z hr
  rw [hp]
  refine ⟨mem_univ _, ⟨mem_univ _, h0⟩, ?_⟩
  change ((ULift.up z : ClosureSphere.{u}), halfSpaceOneLift (a + b * (r - 1))) ∈
    (B.sphere i).source
  rw [B.sphere_source]
  exact shellLift_mem_source _ h1

/-- The unit vector of a nonzero vector, as a point of the unit sphere. -/
def shellDir {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem shellDir_smul {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ‖x‖ • ((shellDir hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = x := by
  change ‖x‖ • (‖x‖⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem norm_smul_sphere (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ}
    (hr : 0 ≤ r) : ‖r • (z : EuclideanSpace ℝ (Fin 3))‖ = r := by
  rw [norm_smul, Real.norm_of_nonneg hr, norm_eq_of_mem_sphere z, mul_one]

/-- **Tube lemma.** The collar stays in an open set containing the cap up to a positive height. -/
theorem exists_capCollar_height_mem {T : Set Q.Carrier} (hT : IsOpen T)
    (hcap : range (K.cap i) ⊆ T) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧
      ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ, 0 ≤ p.2 → p.2 ≤ h →
        capCollar K i p ∈ T := by
  let A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
    {p | p.2 < 1} ∩ capCollar K i ⁻¹' T
  have hA : IsOpen A :=
    (continuousOn_capCollar K i).isOpen_inter_preimage
      (isOpen_lt continuous_snd continuous_const) hT
  have hz : (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ ({0} : Set ℝ) ⊆
      A := by
    rintro ⟨z, s⟩ ⟨-, hs⟩
    have hs0 : s = 0 := hs
    subst hs0
    exact ⟨show (0 : ℝ) < 1 by norm_num, hcap (capCollar_zero_mem_range_cap K i z)⟩
  obtain ⟨V, W, -, hW, hUV, hZW, hVW⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hA hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW 0 (hZW rfl)
  refine ⟨min (ε / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun p hp0 hph => ?_⟩
  have hm : p ∈ A := hVW ⟨hUV (mem_univ p.1), hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hp0]
    exact lt_of_le_of_lt hph (lt_of_le_of_lt (min_le_left _ _) (by linarith)))⟩
  exact hm.2

/-- The collar in the coordinates of a chart `φ`, at height `a + b (‖x‖ - 1)`. -/
def shellCoord (φ : PartialDiffeomorph (𝓡 3) Q.model (EuclideanSpace ℝ (Fin 3)) Q.Carrier ∞)
    (a b : ℝ) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  φ.symm (K.core (shellPD i a b hb x))

theorem shellCoord_smul (φ : PartialDiffeomorph (𝓡 3) Q.model (EuclideanSpace ℝ (Fin 3))
      Q.Carrier ∞) (a b : ℝ) (hb : 0 < b)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ} (hr : 0 < r) :
    shellCoord K i φ a b hb (r • (z : EuclideanSpace ℝ (Fin 3))) =
      φ.symm (capCollar K i (z, a + b * (r - 1))) := by
  rw [shellCoord, shellPD_smul i a b hb z hr]
  rfl

/-- The open shell `1/2 < ‖x‖ < 3`. -/
def shellSet : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)) :=
  ⟨{x | 1 / 2 < ‖x‖ ∧ ‖x‖ < 3},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

section Shell

variable (φ : PartialDiffeomorph (𝓡 3) Q.model (EuclideanSpace ℝ (Fin 3)) Q.Carrier ∞)
  {a b : ℝ} (hb : 0 < b) (ha0 : 0 < a - b / 2) (ha1 : a + 2 * b < 1)
  (hT : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ, a - b / 2 ≤ p.2 →
    p.2 ≤ a + 2 * b → capCollar K i p ∈ φ.target)

include ha0 ha1 in
theorem shellSet_mem_source {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ shellSet) :
    x ∈ (shellPD i a b hb).source := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hx.1)
  have h := mem_shellPD_source i a b hb (shellDir hx0) (r := ‖x‖) (norm_pos_iff.mpr hx0)
    (by nlinarith [hx.1, hx.2, hb]) (by nlinarith [hx.1, hx.2, hb])
  rwa [shellDir_smul hx0] at h

include hT in
theorem shellSet_core_mem_target {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ shellSet) :
    K.core (shellPD i a b hb x) ∈ φ.target := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hx.1)
  rw [← shellDir_smul hx0, shellPD_smul i a b hb _ (norm_pos_iff.mpr hx0)]
  exact hT (shellDir hx0, a + b * (‖x‖ - 1)) (by nlinarith [hx.1, hx.2, hb])
    (by nlinarith [hx.1, hx.2, hb])

include ha0 ha1 hT in
theorem contMDiffOn_shellCoord :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (shellCoord K i φ a b hb) shellSet := by
  have h1 : ContMDiffOn (𝓡 3) C.model ∞ (shellPD i a b hb) shellSet :=
    (shellPD i a b hb).contMDiffOn.mono fun x hx => shellSet_mem_source i hb ha0 ha1 hx
  have h2 : ContMDiffOn (𝓡 3) Q.model ∞ (fun x => K.core (shellPD i a b hb x)) shellSet :=
    K.core_embedding.contMDiff.comp_contMDiffOn h1
  exact φ.contMDiffOn_invFun.comp h2 fun x hx =>
    shellSet_core_mem_target K i φ hb hT hx

include ha0 ha1 hT in
theorem isLocalDiffeomorphAt_shellCoord {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ shellSet) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (shellCoord K i φ a b hb) x := by
  have hxs := shellSet_mem_source i hb ha0 ha1 hx
  have hyt := shellSet_core_mem_target K i φ hb hT hx
  have h1 := (shellPD i a b hb).isLocalDiffeomorphAt (𝓡 3) C.model ∞ hxs
  have hint : C.model.IsInteriorPoint (shellPD i a b hb x) :=
    (h1.isInteriorPoint_iff (by simp)).mp BoundarylessManifold.isInteriorPoint
  obtain ⟨hbij, -⟩ := K.core_positive _ hint
  have h3 := φ.symm.isLocalDiffeomorphAt Q.model (𝓡 3) ∞ hyt
  have hcore : (mfderiv C.model Q.model K.core (shellPD i a b hb x)).IsInvertible :=
    ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv, rfl⟩
  have hinv : (mfderiv (𝓡 3) (𝓡 3) (shellCoord K i φ a b hb) x).IsInvertible := by
    have hd1 : MDifferentiableAt (𝓡 3) C.model (shellPD i a b hb) x := h1.mdifferentiableAt
      (by simp)
    have hd2 : MDifferentiableAt C.model Q.model K.core (shellPD i a b hb x) :=
      K.core_embedding.contMDiff.mdifferentiableAt (by simp)
    have hd3 : MDifferentiableAt Q.model (𝓡 3) φ.symm (K.core (shellPD i a b hb x)) :=
      h3.mdifferentiableAt (by simp)
    have hcomp : shellCoord K i φ a b hb = φ.symm ∘ K.core ∘ shellPD i a b hb := rfl
    rw [hcomp, mfderiv_comp x hd3 (hd2.comp x hd1), mfderiv_comp x hd2 hd1]
    exact (h3.isInvertible_mfderiv (by simp)).comp
      (hcore.comp (h1.isInvertible_mfderiv (by simp)))
  exact DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    shellSet.isOpen hx (contMDiffOn_shellCoord K i φ hb ha0 ha1 hT) hinv

include ha0 ha1 hT in
theorem injOn_shellCoord : InjOn (shellCoord K i φ a b hb) shellSet := by
  intro x hx y hy h
  have hxs := shellSet_mem_source i hb ha0 ha1 hx
  have hys := shellSet_mem_source i hb ha0 ha1 hy
  have hc := φ.symm.injOn (shellSet_core_mem_target K i φ hb hT hx)
    (shellSet_core_mem_target K i φ hb hT hy) h
  exact (shellPD i a b hb).injOn hxs hys (core_injective K hc)

/-- **The shell partial diffeomorphism**: the collar in the coordinates of `φ` near the unit
sphere. -/
def shellPartialDiffeomorph :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞ :=
  DifferentialGeometry.Geometry.Collapse.partialDiffeomorphOfInjOn (shellCoord K i φ a b hb)
    shellSet (contMDiffOn_shellCoord K i φ hb ha0 ha1 hT)
    (DifferentialGeometry.isLocalDiffeomorph_restrict_open shellSet fun x =>
      isLocalDiffeomorphAt_shellCoord K i φ hb ha0 ha1 hT x.property)
    (injOn_shellCoord K i φ hb ha0 ha1 hT)

end Shell

theorem shellCoord_eq (φ : PartialDiffeomorph (𝓡 3) Q.model (EuclideanSpace ℝ (Fin 3))
      Q.Carrier ∞) (a b : ℝ) (hb : 0 < b) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    shellCoord K i φ a b hb x = φ.symm (capCollar K i (shellDir hx, a + b * (‖x‖ - 1))) := by
  conv_lhs => rw [← shellDir_smul hx]
  exact shellCoord_smul K i φ a b hb _ (norm_pos_iff.mpr hx)

/-- The image of the collar below a height, in terms of the cut certificate. -/
theorem capCollar_image_eq (s₀ : ℝ) :
    capCollar K i '' {p | 0 ≤ p.2 ∧ p.2 < s₀} = K.core '' (B.sphere i '' {p | p.2.val 0 < s₀}) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨B.sphere i (ULift.up p.1, halfSpaceOneLift p.2), ⟨_, ?_, rfl⟩, rfl⟩
    change (halfSpaceOneLift p.2).val 0 < s₀
    rw [shellLift_coord, max_eq_left hp.1]
    exact hp.2
  · rintro ⟨c, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨(q.1.down, q.2.val 0), ⟨q.2.property, hq⟩, ?_⟩
    change K.core (B.sphere i (ULift.up q.1.down, halfSpaceOneLift (q.2.val 0))) = _
    rw [shellLift_val]

/-- A partial diffeomorphism's inverse carries the frontier and closure of an open set whose closure
is a compact subset of its target. -/
theorem image_symm_frontier_closure
    (φ : PartialDiffeomorph (𝓡 3) Q.model (EuclideanSpace ℝ (Fin 3)) Q.Carrier ∞)
    {A : Set Q.Carrier} (hA : IsOpen A) (hcl : closure A ⊆ φ.target)
    (hcpt : IsCompact (closure A)) :
    closure (φ.symm '' A) = φ.symm '' closure A ∧
      frontier (φ.symm '' A) = φ.symm '' frontier A := by
  have hcont : ContinuousOn φ.symm (closure A) := φ.contMDiffOn_invFun.continuousOn.mono hcl
  have hc : closure (φ.symm '' A) = φ.symm '' closure A := by
    apply le_antisymm
    · exact closure_minimal (image_mono subset_closure) (hcpt.image_of_continuousOn hcont).isClosed
    · exact hcont.image_closure
  have hAt : A ⊆ φ.target := subset_closure.trans hcl
  have ho : IsOpen (φ.symm '' A) :=
    φ.toOpenPartialHomeomorph.symm.isOpen_image_of_subset_source hA hAt
  refine ⟨hc, ?_⟩
  rw [frontier, frontier, hc, ho.interior_eq, hA.interior_eq]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun h => hn ⟨x, h, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hnx⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨x', hx', he⟩
    exact hnx (φ.symm.injOn (hAt hx') (hcl hx) he ▸ hx')

/-- **A6-a (shell ball chart).** The cap of a relative sphere capping, together with the collar of
its cut sphere, is the closed unit ball of an interior ball chart whose shell `1 ≤ ‖x‖ ≤ 2` IS the
cut collar at heights `s₀ + μ (‖x‖ - 1)`. -/
theorem RelativeSphereCapping.exists_shellBallChart {C Q : CompactCarrier.{u}}
    {B : MixedBoundaryCertificate C} (K : RelativeSphereCapping C Q B) (i : Fin B.sphereCount) :
    ∃ (c : PartialDiffeomorph (𝓡 3) Q.model (EuclideanSpace ℝ (Fin 3)) Q.Carrier ∞)
      (s₀ μ : ℝ) (hs₀ : 0 < s₀) (hμ : 0 < μ), s₀ + μ < 1 ∧
      Metric.closedBall 0 2 ⊆ c.source ∧ c.target ⊆ Q.interior ∧
      (∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
        c (r • (z : EuclideanSpace ℝ (Fin 3))) =
          K.core (B.sphere i (ULift.up z, halfPoint (s₀ + μ * (r - 1))
            (add_nonneg hs₀.le (mul_nonneg hμ.le (sub_nonneg.mpr hr)))))) ∧
      c '' Metric.ball 0 1 =
        range (K.cap i) ∪ K.core '' (B.sphere i '' {p | p.2.val 0 < s₀}) := by
  obtain ⟨φ, hφs, hφI, hφc⟩ := exists_ballChart_of_closedCell_interior (K.cap i)
    (K.cap_embedding i) (cap_isInteriorPoint K i)
  have hcapT : range (K.cap i) ⊆ φ.target := by
    rintro _ ⟨x, rfl⟩
    rw [← hφc x]
    exact φ.map_source (hφs (mem_closedBall_zero_iff.mpr x.property))
  obtain ⟨h, hh0, hh1, hT⟩ := exists_capCollar_height_mem K i φ.open_target hcapT
  have hb : 0 < h / 8 := by linarith
  have ha0 : 0 < h / 2 - h / 8 / 2 := by linarith
  have ha1 : h / 2 + 2 * (h / 8) < 1 := by linarith
  have hT' : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
      h / 2 - h / 8 / 2 ≤ p.2 → p.2 ≤ h / 2 + 2 * (h / 8) → capCollar K i p ∈ φ.target :=
    fun p h1 h2 => hT p (by linarith) (by linarith)
  let F := shellPartialDiffeomorph K i φ hb ha0 ha1 hT'
  have hF (x : EuclideanSpace ℝ (Fin 3)) : F x = shellCoord K i φ (h / 2) (h / 8) hb x := rfl
  have hFs : F.source = shellSet := rfl
  have hFeq (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) : F x =
      φ.symm (capCollar K i (shellDir hx, h / 2 + h / 8 * (‖x‖ - 1))) := by
    rw [hF, shellCoord_eq K i φ _ _ hb hx]
  have ha : 0 < h / 2 := by linarith
  have ha' : h / 2 < 1 := by linarith
  let A := capRegion K i (h / 2)
  have hA : IsOpen A := isOpen_capRegion K i ha ha'.le
  have hclA : closure A = capRegionClosed K i (h / 2) := closure_capRegion K i ha ha'
  have hAT : capRegionClosed K i (h / 2) ⊆ φ.target := by
    rintro y (hy | ⟨p, hp, rfl⟩)
    · exact hcapT hy
    · exact hT p hp.1 (by linarith [hp.2])
  have hcpt := isCompact_capRegionClosed K i ha'
  obtain ⟨hcl, hfr⟩ := image_symm_frontier_closure φ hA (hclA ▸ hAT) (hclA ▸ hcpt)
  rw [hclA] at hcl
  rw [frontier_capRegion K i ha ha'] at hfr
  have hcont : ContinuousOn φ.symm φ.target := φ.contMDiffOn_invFun.continuousOn
  have hAt : A ⊆ φ.target := (capRegion_subset_closed K i _).trans hAT
  let U := φ.symm '' A
  have hUo : IsOpen U := φ.toOpenPartialHomeomorph.symm.isOpen_image_of_subset_source hA hAt
  have hUb : Bornology.IsBounded U :=
    (hcpt.image_of_continuousOn (hcont.mono hAT)).isBounded.subset
      (image_mono (capRegion_subset_closed K i _))
  have hUc : IsPreconnected U := (isPreconnected_capRegion K i ha ha').image _ (hcont.mono hAt)
  have hS : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ F.source := by
    intro x hx
    rw [hFs]
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    exact ⟨by rw [hn]; norm_num, by rw [hn]; norm_num⟩
  have hfront : frontier U = F '' Metric.sphere 0 1 := by
    rw [hfr]
    ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨(p.1 : EuclideanSpace ℝ (Fin 3)), p.1.property, ?_⟩
      have hp0 : (p.1 : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
        intro h0
        have := norm_eq_of_mem_sphere p.1
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      rw [hFeq _ hp0]
      have hd : shellDir hp0 = p.1 := by
        apply Subtype.ext
        change ‖(p.1 : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (p.1 : EuclideanSpace ℝ (Fin 3)) = p.1
        rw [norm_eq_of_mem_sphere p.1, inv_one, one_smul]
      rw [hd, norm_eq_of_mem_sphere p.1, sub_self, mul_zero, add_zero]
      change φ.symm (capCollar K i (p.1, h / 2)) = φ.symm (capCollar K i p)
      rw [show (p.1, h / 2) = p from Prod.ext rfl hp.symm]
    · rintro ⟨x, hx, rfl⟩
      have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
      rw [hFeq x hx0, hn, sub_self, mul_zero, add_zero]
      exact ⟨_, ⟨(shellDir hx0, h / 2), rfl, rfl⟩, rfl⟩
  have hin : ∀ x ∈ F.source, ‖x‖ < 1 → F x ∈ U := by
    intro x hx hx1
    rw [hFs] at hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hx.1)
    rw [hFeq x hx0]
    refine ⟨_, Or.inr ⟨(shellDir hx0, h / 2 + h / 8 * (‖x‖ - 1)), ⟨?_, ?_⟩, rfl⟩, rfl⟩
    · change 0 ≤ h / 2 + h / 8 * (‖x‖ - 1)
      nlinarith [hx.1]
    · change h / 2 + h / 8 * (‖x‖ - 1) < h / 2
      nlinarith
  have hout : ∀ x ∈ F.source, 1 < ‖x‖ → F x ∉ closure U := by
    intro x hx hx1 hcx
    rw [hFs] at hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hx.1)
    rw [hcl, hFeq x hx0] at hcx
    obtain ⟨y, hy, he⟩ := hcx
    have hht : h / 2 < h / 2 + h / 8 * (‖x‖ - 1) := by nlinarith
    have hht1 : h / 2 + h / 8 * (‖x‖ - 1) < 1 := by nlinarith [hx.2]
    have hmem : capCollar K i (shellDir hx0, h / 2 + h / 8 * (‖x‖ - 1)) ∈ φ.target :=
      hT' _ (by nlinarith [hx.1]) (by nlinarith [hx.2])
    have hye := φ.symm.injOn (hAT hy) hmem he
    rcases hy with hy | ⟨q, hq, rfl⟩
    · rw [hye] at hy
      exact capCollar_notMem_range_cap K i _ (by linarith) hht1 hy
    · have hqe := capCollar_injOn K i ⟨hq.1, by linarith [hq.2]⟩
        ⟨by linarith, hht1⟩ hye
      have := hq.2
      rw [hqe] at this
      change h / 2 + h / 8 * (‖x‖ - 1) ≤ h / 2 at this
      linarith
  obtain ⟨G, hGU, hGcl, V, hVo, hSV, hVF, hGF⟩ :=
    GC.Seifert.SplitTube.exists_ballFill_of_shell F hS hUo hUb hUc hfront hin hout
  let Hm : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun x => if ‖x‖ < 1 then G x else F x
  have hHm (x : EuclideanSpace ℝ (Fin 3)) : Hm x = if ‖x‖ < 1 then G x else F x := rfl
  have hHG : ∀ x, (‖x‖ < 1 ∨ x ∈ V) → Hm =ᶠ[𝓝 x] G := by
    intro x hx
    rcases hx with hx | hx
    · filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      rw [hHm, ite_eq_left hy]
    · filter_upwards [hVo.mem_nhds hx] with y hy
      by_cases hy1 : ‖y‖ < 1
      · rw [hHm, ite_eq_left hy1]
      · rw [hHm, ite_eq_right hy1]
        exact (hGF hy).symm
  have hHF : ∀ x, 1 < ‖x‖ → Hm =ᶠ[𝓝 x] F := by
    intro x hx
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    rw [hHm, ite_eq_right (not_lt.mpr hy.le)]
  have hcase : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 3 →
      (‖x‖ < 1 ∨ x ∈ V) ∨ (1 < ‖x‖ ∧ x ∈ F.source) := by
    intro x hx
    rcases lt_trichotomy ‖x‖ 1 with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (hSV (mem_sphere_zero_iff_norm.mpr h1)))
    · refine Or.inr ⟨h1, ?_⟩
      rw [hFs]
      exact ⟨by linarith, hx⟩
  let O : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)) :=
    ⟨Metric.ball 0 3, Metric.isOpen_ball⟩
  have hHsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Hm O := by
    intro x hx
    have hx3 : ‖x‖ < 3 := mem_ball_zero_iff.mp hx
    rcases hcase x hx3 with hg | ⟨h1, hf⟩
    · exact (G.contMDiff.contMDiffAt.congr_of_eventuallyEq (hHG x hg)).contMDiffWithinAt
    · exact ((F.contMDiffOn.contMDiffAt (F.open_source.mem_nhds hf)).congr_of_eventuallyEq
        (hHF x h1)).contMDiffWithinAt
  have hHloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ Hm O := by
    intro x
    rcases hcase x (mem_ball_zero_iff.mp x.property) with hg | ⟨h1, hf⟩
    · exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hHG x hg)
        (G.isLocalDiffeomorph x)
    · exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hHF x h1)
        (F.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hf)
  have hGin : ∀ x, ‖x‖ < 1 → G x ∈ U := fun x hx =>
    hGU ▸ ⟨x, mem_ball_zero_iff.mpr hx, rfl⟩
  have hkey : ∀ x y, ‖x‖ < 1 → 1 ≤ ‖y‖ → ‖y‖ < 3 → Hm x = Hm y → False := by
    intro x y hx hy hy3 he
    rw [hHm, hHm, ite_eq_left hx, ite_eq_right (not_lt.mpr hy)] at he
    rcases hy.lt_or_eq with hy1 | hy1
    · have hys : y ∈ F.source := by
        rw [hFs]
        exact ⟨by linarith, hy3⟩
      exact hout y hys hy1 (he ▸ subset_closure (hGin x hx))
    · have hyV : y ∈ V := hSV (mem_sphere_zero_iff_norm.mpr hy1.symm)
      rw [← hGF hyV] at he
      have hxy := G.injective he
      rw [hxy] at hx
      linarith
  have hHinj : InjOn Hm O := by
    intro x hx y hy hxy
    have hx3 : ‖x‖ < 3 := mem_ball_zero_iff.mp hx
    have hy3 : ‖y‖ < 3 := mem_ball_zero_iff.mp hy
    rcases lt_or_ge ‖x‖ 1 with hx1 | hx1 <;> rcases lt_or_ge ‖y‖ 1 with hy1 | hy1
    · rw [hHm, hHm, ite_eq_left hx1, ite_eq_left hy1] at hxy
      exact G.injective hxy
    · exact (hkey x y hx1 hy1 hy3 hxy).elim
    · exact (hkey y x hy1 hx1 hx3 hxy.symm).elim
    · rw [hHm, hHm, ite_eq_right (not_lt.mpr hx1), ite_eq_right (not_lt.mpr hy1)] at hxy
      have hxs : x ∈ F.source := by
        rw [hFs]
        exact ⟨by linarith, hx3⟩
      have hys : y ∈ F.source := by
        rw [hFs]
        exact ⟨by linarith, hy3⟩
      exact F.injOn hxs hys hxy
  let Hpd := DifferentialGeometry.Geometry.Collapse.partialDiffeomorphOfInjOn Hm O hHsm
    (DifferentialGeometry.isLocalDiffeomorph_restrict_open O hHloc) hHinj
  have hHpd (x : EuclideanSpace ℝ (Fin 3)) : Hpd x = Hm x := rfl
  have hHφ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 3 → Hm x ∈ φ.source := by
    intro x hx
    by_cases hx1 : ‖x‖ < 1
    · rw [hHm, ite_eq_left hx1]
      obtain ⟨y, hy, he⟩ := hGin x hx1
      rw [← he]
      exact φ.map_target (hAt hy)
    · rw [hHm, ite_eq_right hx1]
      have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
      rw [hFeq x hx0]
      exact φ.map_target (hT' _ (by nlinarith) (by nlinarith))
  refine ⟨Hpd.trans φ, h / 2, h / 8, ha, hb, by linarith, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx3 : ‖x‖ < 3 := lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) (by norm_num)
    exact ⟨mem_ball_zero_iff.mpr hx3, hHφ x hx3⟩
  · intro y hy
    exact hφI y hy.1
  · intro z r hr hr2
    have hn : ‖r • (z : EuclideanSpace ℝ (Fin 3))‖ = r := norm_smul_sphere z (by linarith)
    change φ (Hm (r • (z : EuclideanSpace ℝ (Fin 3)))) = _
    rw [hHm, ite_eq_right (by rw [hn]; linarith), hF,
      shellCoord_smul K i φ _ _ hb z (by linarith : (0 : ℝ) < r)]
    have hmem := hT' (z, h / 2 + h / 8 * (r - 1)) (by change _ ≤ h / 2 + h / 8 * (r - 1); nlinarith)
      (by change h / 2 + h / 8 * (r - 1) ≤ _; nlinarith)
    have hr' : φ.toPartialEquiv (φ.symm.toPartialEquiv (capCollar K i (z, h / 2 + h / 8 * (r - 1)))) =
        capCollar K i (z, h / 2 + h / 8 * (r - 1)) := φ.right_inv hmem
    rw [hr', capCollar, halfPoint_eq_halfSpaceOneLift]
  · rw [← capCollar_image_eq]
    change (Hpd.trans φ) '' Metric.ball 0 1 = A
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
      obtain ⟨w, hw, he⟩ := hGin x hx1
      change φ (Hm x) ∈ A
      rw [hHm, ite_eq_left hx1, ← he]
      have hr' : φ (φ.symm w) = w := φ.right_inv (hAt hw)
      rw [hr']
      exact hw
    · intro hy
      have hyU : φ.symm y ∈ U := ⟨y, hy, rfl⟩
      rw [← hGU] at hyU
      obtain ⟨x, hx, hxe⟩ := hyU
      refine ⟨x, hx, ?_⟩
      have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
      change φ (Hm x) = y
      rw [hHm, ite_eq_left hx1, hxe]
      exact φ.right_inv (hAt hy)

end GC.GraphManifold.Assembly
