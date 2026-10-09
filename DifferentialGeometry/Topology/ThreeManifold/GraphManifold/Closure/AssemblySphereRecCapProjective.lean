import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapProjectiveShell
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapBall
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSides
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyFaced
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplement
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# FC42 sphere recursion, packet S3b: a punctured `ℝP³` side and its cap make `ℝP³`

Lane ASM-SPH3b (successor of ASM-SPH3). For the cut-and-capped data `X : SphereCutCapped W S E`
and a piece `P` of `W` on side `j` of the seam, whose half collar of side `j` lies in it, whose model
boundary is exactly the seam sphere, and which is embedded by `f` into a closed three-manifold `Y`
with image the complement of the open unit ball of a chart `c` (the data of a punctured-`ℝP³`
zero vertex):

* `liftPiece_mem_range_cap_iff`: a lifted point lies in the cap of its copy exactly when it is a
  model-boundary point;
* `nonempty_capUnion_closedDiffeomorph`: the union `lift ∪ cap` is diffeomorphic to `Y` — for the
  ACTUAL attaching map of the capping. The ball complement of `Y` outside `c (B(3/2))` goes into
  the union by `g ∘ f⁻¹` (`exists_partialDiffeomorph_comp_inv`); the shell `c (B̄(3/2) ∖ B(1))`
  lifted by `g ∘ f⁻¹ ∘ c` and the cap make one ball chart (`exists_ballChart_of_shell_cap`), whose
  open ball is the complement; `exists_diffeomorph_of_ball_complement_and_ball` (no Smale) glues.

Certificate level (`DecompositionCertificate`): the model boundary of a punctured-`ℝP³` side is the
seam sphere (its boundary image is a two-sphere, hence preconnected, hence the seam face,
`face_eq_boundaryImage_of_isPreconnected`); the capped side is the component of the capped carrier
containing its cap, and that component is the fixed `ℝP³`
(`componentCarrier_projective_of_puncturedRP3`, packet S3b, frozen statement).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
  GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsCapProj_ASMSPH3b : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothCapProj_ASMSPH3b : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-! ## The radial shell at its ends; the homothety by `3 / 2` -/

theorem shellRadial_iccZero (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    shellRadial (z, iccZero) = z := by
  change (1 + (0 : ℝ) / 2) • (z : EuclideanSpace ℝ (Fin 3)) = z
  simp

theorem shellRadial_iccOne (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    shellRadial (z, iccOne) = (3 / 2 : ℝ) • (z : EuclideanSpace ℝ (Fin 3)) := by
  change (1 + (1 : ℝ) / 2) • (z : EuclideanSpace ℝ (Fin 3)) = _
  norm_num

/-- Every point of the shell `1 ≤ ‖w‖ < 3 / 2` is a radial shell point off the outer end. -/
theorem exists_shellRadial_eq {w : EuclideanSpace ℝ (Fin 3)} (h1 : 1 ≤ ‖w‖) (h2 : ‖w‖ < 3 / 2) :
    ∃ p, shellRadial p = w ∧ (p.2 : ℝ) < 1 := by
  have hw0 : ‖w‖ ≠ 0 := by linarith
  have hz : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0]
  refine ⟨(⟨_, hz⟩, ⟨2 * (‖w‖ - 1), by linarith, by linarith⟩), ?_, ?_⟩
  · change (1 + 2 * (‖w‖ - 1) / 2) • (‖w‖⁻¹ • w) = w
    rw [smul_smul, show (1 + 2 * (‖w‖ - 1) / 2 : ℝ) = ‖w‖ by ring, mul_inv_cancel₀ hw0, one_smul]
  · change 2 * (‖w‖ - 1) < 1
    linarith

/-- The homothety by `3 / 2` of `ℝ³`. -/
def homothetyThreeHalves : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace ℝ (Fin 3)) ∞ :=
  Diffeomorph.toPartialDiffeomorph
    { toFun x := (3 / 2 : ℝ) • x
      invFun x := (2 / 3 : ℝ) • x
      left_inv x := by
        change (2 / 3 : ℝ) • (3 / 2 : ℝ) • x = x
        rw [smul_smul]
        norm_num
      right_inv x := by
        change (3 / 2 : ℝ) • (2 / 3 : ℝ) • x = x
        rw [smul_smul]
        norm_num
      contMDiff_toFun := (contDiff_const_smul (3 / 2 : ℝ)).contMDiff
      contMDiff_invFun := (contDiff_const_smul (2 / 3 : ℝ)).contMDiff }

theorem homothetyThreeHalves_apply (x : EuclideanSpace ℝ (Fin 3)) :
    homothetyThreeHalves x = (3 / 2 : ℝ) • x :=
  rfl

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- A cap point lies in the core only on the boundary sphere of the cell. -/
theorem norm_eq_one_of_cap_mem_range_core (j : Fin 2) {x : ClosedCell 3}
    (hx : X.capping.cap (Fin.cast X.h2.symm j) x ∈ range X.capping.core) : ‖x.val‖ = 1 := by
  have hmem : X.capping.cap (Fin.cast X.h2.symm j) x ∈
      range X.capping.core ∩ range (X.capping.cap (Fin.cast X.h2.symm j)) := ⟨hx, x, rfl⟩
  rw [X.capping.core_cap_intersection] at hmem
  obtain ⟨z, hz⟩ := hmem
  let w := (X.capping.attaching (Fin.cast X.h2.symm j)).symm z
  have hcz : X.capping.cap (Fin.cast X.h2.symm j) (closureSphereToBall w) =
      X.capping.cap (Fin.cast X.h2.symm j) x := by
    rw [X.capping.boundary_eq, Diffeomorph.apply_symm_apply]
    exact hz
  have hxe := (X.capping.cap_embedding _).isEmbedding.injective hcz
  have hw : (closureSphereToBall w).val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := w.down.2
  rw [← hxe]
  exact mem_sphere_zero_iff_norm.mp hw

section Projective

variable (P : PieceEmbedding W) (j : Fin 2)
  (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)

variable {P} in
/-- For a piece whose model boundary is the seam sphere, a lifted point lies in the cap of its copy
exactly when it is a model-boundary point. -/
theorem liftPiece_mem_range_cap_iff (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere)
    {q : P.Piece} :
    (X.liftPiece P j hside).map q ∈ range (X.capping.cap (Fin.cast X.h2.symm j)) ↔
      (𝓡∂ 3).IsBoundaryPoint q := by
  have hzero : S.zeroSphere ⊆ range P.map := by
    rw [← hbd]
    exact image_subset_range _ _
  constructor
  · intro h
    have hmem : (X.liftPiece P j hside).map q ∈ range (X.liftPiece P j hside).map ∩
        range (X.capping.cap (Fin.cast X.h2.symm j)) := ⟨⟨q, rfl⟩, h⟩
    rw [X.range_liftPiece_inter_cap P j hside hzero] at hmem
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨q', hq'⟩ := hzero ⟨z, rfl⟩
    have hq'q : q' = q :=
      (X.liftPiece P j hside).injective ((X.liftPiece_map_of_mem P j hside hq').trans hz)
    subst hq'q
    have hx : P.map q' ∈ S.zeroSphere := ⟨z, hq'.symm⟩
    rw [← hbd] at hx
    obtain ⟨q'', hq'', hq''q⟩ := hx
    rw [← P.injective hq''q]
    exact hq''
  · intro h
    have hx : P.map q ∈ S.zeroSphere := hbd ▸ ⟨q, h, rfl⟩
    obtain ⟨z, hz⟩ := hx
    rw [X.liftPiece_map_of_mem P j hside hz.symm]
    exact X.core_cutSphere_mem_range_cap j z

/-- **Punctured `Y` ∪ cap = `Y`** (actual attaching map), on any open set equal to the union. -/
theorem nonempty_closedDiffeomorph_of_capUnion {Y : ConnectedClosedOrientedManifold.{u} 3}
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      Y.Carrier ∞)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    {f : P.Piece → Y.Carrier} (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere)
    (U : TopologicalSpace.Opens X.Q.Carrier)
    (hUeq : (U : Set X.Q.Carrier) =
      range (X.liftPiece P j hside).map ∪ range (X.capping.cap (Fin.cast X.h2.symm j))) :
    Nonempty (U ≃ₘ⟮X.Q.model, 𝓡 3⟯ Y.Carrier) := by
  set L := X.liftPiece P j hside with hLdef
  set J := Fin.cast X.h2.symm j with hJdef
  have hc1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ c.source :=
    (Metric.closedBall_subset_closedBall (by norm_num)).trans hc
  have hcinj : ∀ {w w'}, w ∈ c.source → w' ∈ c.source → c w = c w' → w = w' :=
    fun hw hw' h => c.toPartialEquiv.injOn hw hw' h
  have hc2 : ∀ {w : EuclideanSpace ℝ (Fin 3)}, ‖w‖ ≤ 2 → w ∈ c.source := fun hw =>
    hc (mem_closedBall_zero_iff.mpr hw)
  have hint := X.liftPiece_mem_interior P j hside
    (range_subset_interior_of_boundary_eq_zeroSphere P hbd)
  have hU : ∀ y ∈ U, X.Q.model.IsInteriorPoint y := by
    intro y hy
    have hy' : y ∈ range L.map ∪ range (X.capping.cap J) := by
      rw [← hUeq]
      exact hy
    rcases hy' with ⟨q, rfl⟩ | hy'
    · exact hint q
    · exact range_relativeSphereCap_subset_interior X.capping _ hy'
  have hLU : ∀ q, L.map q ∈ U := fun q => by
    change L.map q ∈ (U : Set X.Q.Carrier)
    rw [hUeq]
    exact Or.inl ⟨q, rfl⟩
  have hcapU : ∀ x, X.capping.cap J x ∈ U := fun x => by
    change X.capping.cap J x ∈ (U : Set X.Q.Carrier)
    rw [hUeq]
    exact Or.inr ⟨x, rfl⟩
  let LU : P.Piece → U := fun q => ⟨L.map q, hLU q⟩
  let capU : ClosedCell 3 → U := fun x => ⟨X.capping.cap J x, hcapU x⟩
  have hLUs : ContMDiff (𝓡∂ 3) X.Q.model ∞ LU := (ContMDiff.subtypeVal_comp_iff U LU).mp L.smooth
  have hLUb : ∀ q, Bijective (mfderiv (𝓡∂ 3) X.Q.model LU q) := fun q => by
    rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U LU q]
    exact L.mfderiv_bijective q
  have hcapUs : ContMDiff (𝓡∂ 3) X.Q.model ∞ capU :=
    (ContMDiff.subtypeVal_comp_iff U capU).mp (X.capping.cap_embedding J).contMDiff
  have hcapUb : ∀ x, Bijective (mfderiv (𝓡∂ 3) X.Q.model capU x) := fun x => by
    rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U capU x]
    exact X.mfderiv_cap_bijective J x
  have hUb : BoundarylessManifold X.Q.model U := boundarylessManifold_of_forall_isInteriorPoint U hU
  -- the interior atlas
  let := DifferentialGeometry.Manifold.interiorChartedSpace X.Q.model ∞ (M := U)
  have := DifferentialGeometry.Manifold.interiorIsManifold X.Q.model ∞ (M := U)
  let Dd := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph X.Q.model ∞ (M := U)
  have hDb : ∀ y : U, Bijective (mfderiv X.Q.model (𝓡 3) Dd y) := fun y =>
    (Dd.mfderivToContinuousLinearEquiv (by simp) y).bijective
  let g : P.Piece → U := Dd ∘ LU
  have hg : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ g := Dd.contMDiff.comp hLUs
  have hgi : Injective g := fun q q' h => L.injective (congrArg Subtype.val (Dd.injective h))
  have hgb : ∀ q, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) g q) := fun q => by
    rw [mfderiv_comp q (Dd.contMDiff.mdifferentiableAt (by simp)) (hLUs.mdifferentiableAt (by simp))]
    exact (hDb _).comp (hLUb q)
  have hgval : ∀ q, (g q : X.Q.Carrier) = L.map q := fun _ => rfl
  let cap' : ClosedCell 3 → U := Dd ∘ capU
  have hcap' : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ cap' := Dd.contMDiff.comp hcapUs
  have hcap'i : Injective cap' := fun x x' h =>
    (X.capping.cap_embedding J).isEmbedding.injective (congrArg Subtype.val (Dd.injective h))
  have hcap'b : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) cap' x) := fun x => by
    rw [mfderiv_comp x (Dd.contMDiff.mdifferentiableAt (by simp))
      (hcapUs.mdifferentiableAt (by simp))]
    exact (hDb _).comp (hcapUb x)
  have hcapval : ∀ x, (cap' x : X.Q.Carrier) = X.capping.cap J x := fun _ => rfl
  -- boundary bookkeeping
  have hbdf : ∀ q, (𝓡∂ 3).IsBoundaryPoint q ↔ f q ∈ c '' Metric.sphere 0 1 := fun _ =>
    isBoundaryPoint_iff_mem_image_sphere c hf hc1 hrange
  have hLcap : ∀ q, L.map q ∈ range (X.capping.cap J) ↔ (𝓡∂ 3).IsBoundaryPoint q := fun _ =>
    X.liftPiece_mem_range_cap_iff j hside hbd
  have hcapcore : ∀ x, X.capping.cap J x ∈ range L.map → ‖x.val‖ = 1 := by
    rintro x ⟨q, hq⟩
    exact X.norm_eq_one_of_cap_mem_range_core j (hq ▸ ⟨_, rfl⟩)
  have hzero : S.zeroSphere ⊆ range P.map := by
    rw [← hbd]
    exact image_subset_range _ _
  have hcapsphere : ∀ x : ClosedCell 3, ‖x.val‖ = 1 → ∃ q, L.map q = X.capping.cap J x := by
    intro x hx
    let w : ClosureSphere.{u} := ULift.up ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩
    have hw : closureSphereToBall w = x := rfl
    obtain ⟨q, hq⟩ := hzero ⟨X.capping.attaching J w, rfl⟩
    refine ⟨q, ?_⟩
    rw [X.liftPiece_map_of_mem P j hside hq, ← hw, X.capping.boundary_eq]
    rfl
  have hfnot : ∀ {q w}, f q = c w → ‖w‖ ≤ 2 → 1 ≤ ‖w‖ := by
    intro q w hqw hw2
    by_contra hlt
    have hfq : f q ∈ range f := ⟨q, rfl⟩
    rw [hrange] at hfq
    exact hfq ⟨w, mem_ball_zero_iff.mpr (lt_of_not_ge hlt), hqw.symm⟩
  -- the partial diffeomorphism off the closed unit ball and the shell
  obtain ⟨Φ, hΦs, hΦ⟩ := exists_partialDiffeomorph_comp_inv c hf hc1 hrange g hg hgi hgb
  obtain ⟨F₀, hF₀, hF₀i, hF₀b, hF₀q⟩ := exists_shellLift c hf hc hrange g hg hgi hgb
  obtain ⟨G₀, hG₀s, hG₀eq⟩ := exists_ballChart_of_closedCell_bijective cap' hcap' hcap'i hcap'b
  have hF₀r : ∀ p, ‖shellRadial p‖ ≤ 2 := fun p => (norm_shellRadial_le p).trans (by norm_num)
  have hGs : G₀ '' Metric.sphere 0 1 = range fun z => F₀ (z, iccZero) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      let xc : ClosedCell 3 := ⟨x, hxn.le⟩
      obtain ⟨q, hq⟩ := hcapsphere xc hxn
      have hqb : (𝓡∂ 3).IsBoundaryPoint q := (hLcap q).mp (hq ▸ ⟨xc, rfl⟩)
      obtain ⟨z, hz, hzq⟩ := (hbdf q).mp hqb
      let zs : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨z, hz⟩
      obtain ⟨q', hq'f, hq'g⟩ := hF₀q (zs, iccZero)
      rw [shellRadial_iccZero] at hq'f
      have hq'q : q' = q := hf.isEmbedding.injective (hq'f.trans hzq)
      refine ⟨zs, ?_⟩
      change F₀ (zs, iccZero) = G₀ x
      have hGx : G₀ x = cap' xc := hG₀eq xc
      rw [hq'g, hq'q, hGx]
      exact Subtype.ext hq
    · rintro ⟨z, rfl⟩
      obtain ⟨q, hqf, hqg⟩ := hF₀q (z, iccZero)
      rw [shellRadial_iccZero] at hqf
      have hqb : (𝓡∂ 3).IsBoundaryPoint q := (hbdf q).mpr ⟨z, z.2, hqf.symm⟩
      obtain ⟨x, hx⟩ := (hLcap q).mpr hqb
      have hxn : ‖x.val‖ = 1 := hcapcore x ⟨q, hx.symm⟩
      refine ⟨x.val, mem_sphere_zero_iff_norm.mpr hxn, ?_⟩
      change G₀ x.val = F₀ (z, iccZero)
      rw [hG₀eq x, hqg]
      exact Subtype.ext hx
  have hinter : range F₀ ∩ G₀ '' Metric.closedBall 0 1 ⊆ G₀ '' Metric.sphere 0 1 := by
    rintro y ⟨⟨p, rfl⟩, ⟨x, hx, hxy⟩⟩
    obtain ⟨q, -, hqg⟩ := hF₀q p
    let xc : ClosedCell 3 := ⟨x, mem_closedBall_zero_iff.mp hx⟩
    have hxq : X.capping.cap J xc = L.map q := by
      rw [← hcapval, ← hgval, ← hqg, ← hxy, hG₀eq xc]
    have hxn : ‖x‖ = 1 := hcapcore xc ⟨q, hxq.symm⟩
    exact ⟨x, mem_sphere_zero_iff_norm.mpr hxn, hxy⟩
  obtain ⟨A, hAsrc, hAcl, hAs⟩ :=
    exists_ballChart_of_shell_cap F₀ hF₀ hF₀i hF₀b G₀ hG₀s hGs hinter
  have hAball : A '' Metric.ball 0 1 = A '' Metric.closedBall 0 1 \ A '' Metric.sphere 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, ball_subset_closedBall hx, rfl⟩, ?_⟩
      rintro ⟨x', hx', hxx'⟩
      have hxe : x' = x := A.toPartialEquiv.injOn (hAsrc (sphere_subset_closedBall hx'))
        (hAsrc (ball_subset_closedBall hx)) hxx'
      rw [hxe] at hx'
      exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hx')
    · rintro ⟨⟨x, hx, rfl⟩, hns⟩
      refine ⟨x, mem_ball_zero_iff.mpr (lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx) ?_), rfl⟩
      intro hxn
      exact hns ⟨x, mem_sphere_zero_iff_norm.mpr hxn, rfl⟩
  -- the ball chart of `Y` of radius `3 / 2`
  let b := homothetyThreeHalves.trans c
  have hbapp : ∀ x, b x = c ((3 / 2 : ℝ) • x) := fun _ => rfl
  have hb1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ b.source := by
    intro x hx
    rw [PartialDiffeomorph.trans_source]
    refine ⟨mem_univ _, hc2 ?_⟩
    rw [homothetyThreeHalves_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have := mem_closedBall_zero_iff.mp hx
    nlinarith
  have hbmem : ∀ y, y ∈ b '' Metric.ball 0 1 ↔ ∃ w, ‖w‖ < 3 / 2 ∧ c w = y := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(3 / 2 : ℝ) • x, ?_, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have := mem_ball_zero_iff.mp hx
      nlinarith
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(2 / 3 : ℝ) • w, ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        nlinarith
      · rw [hbapp, smul_smul]
        norm_num
  have hcb : ∀ {w : EuclideanSpace ℝ (Fin 3)}, ‖w‖ < 3 / 2 → c w ∈ b '' Metric.ball 0 1 :=
    fun hw => (hbmem _).mpr ⟨_, hw, rfl⟩
  have hP : (b '' Metric.ball 0 1)ᶜ ⊆ Φ.source := by
    rw [hΦs]
    rintro y hy ⟨w, hw, rfl⟩
    exact hy (hcb (by linarith [mem_closedBall_zero_iff.mp hw]))
  have hU' : ∀ y, y ∈ Φ '' (b '' Metric.ball 0 1)ᶜ ↔
      ∃ q, f q ∉ b '' Metric.ball 0 1 ∧ g q = y := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxr : x ∈ range f := by
        rw [hrange]
        rintro ⟨w, hw, rfl⟩
        exact hx (hcb (by linarith [mem_ball_zero_iff.mp hw]))
      obtain ⟨q, rfl⟩ := hxr
      exact ⟨q, hx, (hΦ q (hP hx)).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨f q, hq, hΦ q (hP hq)⟩
  have hGo : A '' Metric.ball 0 1 = (Φ '' (b '' Metric.ball 0 1)ᶜ)ᶜ := by
    rw [hAball, hAcl, hAs]
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩ hyU
      obtain ⟨q, hqb, rfl⟩ := (hU' _).mp hyU
      rcases hy1 with ⟨p, hp⟩ | ⟨x, hx, hxy⟩
      · obtain ⟨q', hq'f, hq'g⟩ := hF₀q p
        have hq'q : q' = q := hgi (hq'g.symm.trans hp)
        subst hq'q
        by_cases ht : (p.2 : ℝ) = 1
        · refine hy2 ⟨p.1, ?_⟩
          have hp1 : p = (p.1, iccOne) := Prod.ext rfl (Subtype.ext ht)
          change F₀ (p.1, iccOne) = _
          rw [← hp1]
          exact hp
        · have ht1 : (p.2 : ℝ) < 1 := lt_of_le_of_ne p.2.2.2 ht
          refine hqb (hq'f ▸ hcb ?_)
          rw [norm_shellRadial]
          linarith
      · let xc : ClosedCell 3 := ⟨x, mem_closedBall_zero_iff.mp hx⟩
        have hxq : L.map q = X.capping.cap J xc := by
          rw [← hcapval, ← hgval, ← hxy, hG₀eq xc]
        obtain ⟨w, hw, hwq⟩ := (hbdf q).mp ((hLcap q).mp ⟨xc, hxq.symm⟩)
        refine hqb (hwq ▸ hcb ?_)
        rw [mem_sphere_zero_iff_norm.mp hw]
        norm_num
    · intro hyU
      have hy : (y : X.Q.Carrier) ∈ range L.map ∪ range (X.capping.cap J) := by
        rw [← hUeq]
        exact y.2
      rcases hy with ⟨q, hq⟩ | ⟨x, hx⟩
      · have hyq : y = g q := Subtype.ext hq.symm
        have hqb : f q ∈ b '' Metric.ball 0 1 := by
          by_contra hqb
          exact hyU ((hU' y).mpr ⟨q, hqb, hyq.symm⟩)
        obtain ⟨w, hw, hwq⟩ := (hbmem _).mp hqb
        have hw1 : 1 ≤ ‖w‖ := hfnot hwq.symm (by linarith)
        obtain ⟨p, hpw, hp1⟩ := exists_shellRadial_eq hw1 hw
        obtain ⟨q', hq'f, hq'g⟩ := hF₀q p
        rw [hpw, hwq] at hq'f
        have hq'q : q' = q := hf.isEmbedding.injective hq'f
        subst hq'q
        refine ⟨Or.inl ⟨p, hq'g.trans hyq.symm⟩, ?_⟩
        rintro ⟨z, hz⟩
        have hpz : (z, iccOne) = p := hF₀i (hz.trans (hq'g.trans hyq.symm).symm)
        rw [← hpz] at hp1
        exact (lt_irrefl _) hp1
      · have hyx : y = cap' x := Subtype.ext hx.symm
        refine ⟨Or.inr ⟨x.val, mem_closedBall_zero_iff.mpr x.2, (hG₀eq x).trans hyx.symm⟩, ?_⟩
        rintro ⟨z, hz⟩
        have hz' : F₀ (z, iccOne) = y := hz
        obtain ⟨q, hqf, hqg⟩ := hF₀q (z, iccOne)
        have hqx : L.map q = X.capping.cap J x := by
          rw [← hgval, ← hqg, hz', hyx]
          exact hcapval x
        obtain ⟨w, hw, hwq⟩ := (hbdf q).mp ((hLcap q).mp ⟨x, hqx.symm⟩)
        rw [shellRadial_iccOne] at hqf
        have hz2 : ‖(3 / 2 : ℝ) • (z : EuclideanSpace ℝ (Fin 3))‖ = 3 / 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), norm_eq_of_mem_sphere,
            mul_one]
        have hwe : w = (3 / 2 : ℝ) • (z : EuclideanSpace ℝ (Fin 3)) :=
          hcinj (hc2 (by rw [mem_sphere_zero_iff_norm.mp hw]; norm_num))
            (hc2 (by rw [hz2]; norm_num)) (hwq.trans hqf)
        have hwn := mem_sphere_zero_iff_norm.mp hw
        rw [hwe, hz2] at hwn
        norm_num at hwn
  obtain ⟨e, -⟩ := exists_diffeomorph_of_ball_complement_and_ball b Φ A hb1 hP hAsrc rfl hGo
  exact ⟨Dd.trans e.symm⟩

/-- **Punctured `Y` ∪ cap = `Y`** (actual attaching map): the lifted piece and the cap of its copy
form an open set of the capped carrier diffeomorphic to `Y`. -/
theorem nonempty_capUnion_closedDiffeomorph {Y : ConnectedClosedOrientedManifold.{u} 3}
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      Y.Carrier ∞)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    {f : P.Piece → Y.Carrier} (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere)
    (hhalf : ∀ z s, 0 ≤ s → s < 1 → S.collar (z, cutSideSign j * s) ∈ range P.map) :
    Nonempty ((⟨_, X.isOpen_capUnion P j hside hbd hhalf⟩ : TopologicalSpace.Opens X.Q.Carrier)
      ≃ₘ⟮X.Q.model, 𝓡 3⟯ Y.Carrier) :=
  X.nonempty_closedDiffeomorph_of_capUnion P j hside c hc hf hrange hbd _ rfl

end Projective

end SphereCutCapped

/-! ## Certificate level -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

section Side

variable (c : Fin D.sphereSeamCount)

/-- The punctured-`ℝP³` data of a side vertex, read on the vertex piece. -/
theorem exists_puncturedRP3_data_of_side (b : Bool) {P : PieceEmbedding W}
    {c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier}
    {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange)) :
    ∃ f' : (D.vertex (D.sphereSide c b)).piece.Piece → projectiveThreeSpaceLift.{u}.Carrier,
      IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f' ∧
      range f' = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1} := by
  rw [hv]
  exact ⟨f, hf, hrange⟩

/-- **The model boundary of a punctured-`ℝP³` side is the seam sphere**: its boundary image is a
two-sphere, hence preconnected, hence the seam face. -/
theorem boundaryImage_eq_zeroSphere_of_puncturedRP3 (b : Bool) {P : PieceEmbedding W}
    {c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier}
    {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange)) :
    (D.vertex (D.sphereSide c b)).boundaryImage = (D.sphereSeam c).zeroSphere := by
  obtain ⟨f', hf', hrange'⟩ := D.exists_puncturedRP3_data_of_side c b hv
  obtain ⟨g, hgc, -, hrg⟩ :=
    (D.vertex (D.sphereSide c b)).piece.exists_sphereTwo_boundary_of_puncturedRP3 c' f' hf' hrange'
  have hS2 : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  have hpre : IsPreconnected (D.vertex (D.sphereSide c b)).boundaryImage := by
    have h := isPreconnected_range hgc
    rw [hrg] at h
    exact h
  obtain ⟨fc, hfo, hfk⟩ := D.sphereSeam_face c b
  rw [← D.face_eq_boundaryImage_of_isPreconnected hpre fc hfo, (D.face_sphereSeam fc c b hfk).1]
  rfl

variable (X : SphereCutCapped W (D.sphereSeam c) E)

/-- The lifted side `b` and the cap of its copy form an open set, when the model boundary of the
side is the seam sphere. -/
theorem isOpen_capUnion_of_boundaryImage (b : Bool)
    (hbd : (D.vertex (D.sphereSide c b)).boundaryImage = (D.sphereSeam c).zeroSphere) :
    IsOpen (range (D.liftVertex c X (D.sphereSide c b)).map ∪
      range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))) := by
  have hcap : X.capping.cap (Fin.cast X.h2.symm (sideCopy (D.vertexSide c (D.sphereSide c b)))) =
      X.capping.cap (Fin.cast X.h2.symm (sideCopy b)) := by
    rw [D.sideCopy_vertexSide c b]
  have hhalf : ∀ z s, 0 ≤ s → s < 1 → (D.sphereSeam c).collar
      (z, cutSideSign (sideCopy (D.vertexSide c (D.sphereSide c b))) * s) ∈
        range (D.vertex (D.sphereSide c b)).piece.map := by
    intro z s hs0 hs1
    rw [D.sideCopy_vertexSide c b]
    exact D.halfCollar_mem_image c b z hs0 hs1
  rw [← hcap]
  exact X.isOpen_capUnion (D.vertex (D.sphereSide c b)).piece
    (sideCopy (D.vertexSide c (D.sphereSide c b)))
    (fun _ _ hp h => D.vertex_side_condition c (D.sphereSide c b) hp h) hbd hhalf

/-- The capped side `b` is a whole component of the capped carrier, the one containing its cap,
when the model boundary of the side is the seam sphere. -/
theorem capUnion_eq_componentPiece_of_boundaryImage (b : Bool)
    (hbd : (D.vertex (D.sphereSide c b)).boundaryImage = (D.sphereSeam c).zeroSphere)
    (DQ : X.Q.Components) :
    range (D.liftVertex c X (D.sphereSide c b)).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) =
      (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b))) : Set X.Q.Carrier) := by
  have hU := D.isOpen_capUnion_of_boundaryImage c X b hbd
  have hUc : IsCompact (range (D.liftVertex c X (D.sphereSide c b)).map ∪
      range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))) :=
    (D.liftVertex c X (D.sphereSide c b)).isCompact_range.union
      (isCompact_range (X.capping.cap _).continuous)
  set U := range (D.liftVertex c X (D.sphereSide c b)).map ∪
    range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))
  set i := X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b))
  have hclopen : IsClopen U := ⟨hUc.isClosed, hU⟩
  have hpi : IsClopen (DQ.piece i : Set X.Q.Carrier) := isClopen_componentsPiece DQ i
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  have hx₀i : X.capping.core (X.cutSphere (sideCopy b) z₀) ∈ (DQ.piece i : Set X.Q.Carrier) :=
    X.sphere_mem_spherePiece DQ _ z₀
  have hx₀U : X.capping.core (X.cutSphere (sideCopy b) z₀) ∈ U :=
    Or.inr (X.core_cutSphere_mem_range_cap _ z₀)
  have hcapconn : IsConnected (range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))) := by
    have := closedCell_three_connectedSpace
    exact isConnected_range (X.capping.cap _).continuous
  have hLconn : IsConnected (range (D.liftVertex c X (D.sphereSide c b)).map) :=
    (D.liftVertex c X (D.sphereSide c b)).isConnected_range
  have hUconn : IsPreconnected U := by
    refine hLconn.isPreconnected.union (X.capping.core (X.cutSphere (sideCopy b) z₀)) ?_
      (X.core_cutSphere_mem_range_cap _ z₀) hcapconn.isPreconnected
    obtain ⟨q, hq⟩ : (D.sphereSeam c).collar (z₀, 0) ∈
        range (D.vertex (D.sphereSide c b)).piece.map := by
      rw [← Vertex.image_eq_range_piece]
      exact D.sphereSeam_zero_mem c b z₀
    exact ⟨q, D.liftVertex_map_of_mem c X b hq⟩
  have hpconn : IsPreconnected (DQ.piece i : Set X.Q.Carrier) := by
    have := DQ.connected i
    exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
  exact Subset.antisymm (hUconn.subset_isClopen hpi ⟨_, hx₀U, hx₀i⟩)
    (hpconn.subset_isClopen hclopen ⟨_, hx₀i, hx₀U⟩)

/-- **S3b, open-set form** (actual attaching map): the lifted punctured-`ℝP³` side and the cap of
its copy form an open set of the capped carrier diffeomorphic to the fixed `ℝP³`. -/
theorem capUnion_projective_of_puncturedRP3 (b : Bool) {P : PieceEmbedding W}
    {c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier}
    {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange)) :
    ∃ hU : IsOpen (range (D.liftVertex c X (D.sphereSide c b)).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))),
      Nonempty ((⟨_, hU⟩ : TopologicalSpace.Opens X.Q.Carrier) ≃ₘ⟮X.Q.model, 𝓡 3⟯
        projectiveThreeSpaceLift.{u}.Carrier) := by
  have hbd := D.boundaryImage_eq_zeroSphere_of_puncturedRP3 c b hv
  obtain ⟨f', hf', hrange'⟩ := D.exists_puncturedRP3_data_of_side c b hv
  have hU := D.isOpen_capUnion_of_boundaryImage c X b hbd
  refine ⟨hU, ?_⟩
  have hcap : X.capping.cap (Fin.cast X.h2.symm (sideCopy (D.vertexSide c (D.sphereSide c b)))) =
      X.capping.cap (Fin.cast X.h2.symm (sideCopy b)) := by
    rw [D.sideCopy_vertexSide c b]
  exact X.nonempty_closedDiffeomorph_of_capUnion (D.vertex (D.sphereSide c b)).piece
    (sideCopy (D.vertexSide c (D.sphereSide c b)))
    (fun _ _ hp h => D.vertex_side_condition c (D.sphereSide c b) hp h) c'.chart
    c'.closedBall_subset_source hf' hrange' hbd ⟨_, hU⟩ (by rw [hcap]; rfl)

end Side

/-! ## S3b: punctured RP³ ∪ cap = RP³ -/

/-- **S3b.** The component of the capped carrier containing the cap of a punctured-`RP³` side is
diffeomorphic to the fixed `RP³` (actual attaching map). -/
theorem componentCarrier_projective_of_puncturedRP3 (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) (b : Bool) {P : PieceEmbedding W}
    {c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier} {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange))
    (DQ : X.Q.Components) :
    Nonempty ((GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)))).Carrier ≃ₘ⟮
      (GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)))).model, 𝓡 3⟯
      projectiveThreeSpaceLift.{u}.Carrier) := by
  obtain ⟨hU, ⟨φ⟩⟩ := D.capUnion_projective_of_puncturedRP3 c X b hv
  have hset := D.capUnion_eq_componentPiece_of_boundaryImage c X b
    (D.boundaryImage_eq_zeroSphere_of_puncturedRP3 c b hv) DQ
  have hopens : (⟨_, hU⟩ : TopologicalSpace.Opens X.Q.Carrier) =
      DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b))) :=
    TopologicalSpace.Opens.ext hset
  rw [hopens] at φ
  exact ⟨φ⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
