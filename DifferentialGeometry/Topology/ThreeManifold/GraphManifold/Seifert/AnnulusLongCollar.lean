import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCollarStraightening
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

/-!
# A long collar across a product annulus piece

Lane N3b, for `MergedSolidTorus` of `Seifert/MoveAbsorb.lean`.

The planar annulus `planarSet 2` (`1/2 ≤ ‖z‖ ≤ 3`) carries for each boundary circle `n` the long
collar `annulusLongCollar n`, `(t, s) ↦ (r_n ∓ s/4) τ_n t` for `0 ≤ s < 10`: the formula of
`planarCollar 2 n` on a longer interval, whose image is everything but the opposite circle
`n.rev` (`annulusLongCollar_or`). Near `s = 10` it is the short collar of `n.rev` read backwards
with the circle coordinate inverted (`annulusLongCollar_near_end`). The depth
`annulusDepth n z = ± (‖z‖ - r_n)` is `s/4` along the collar, and the two depths add up to `5/2`.

A piece `P : ProductFibredPiece T i 2` is `Pₐ × S¹` for an abstract `PlanarBase 2`; the two
smooth embeddings onto `planarModel 2` give a diffeomorphism `planarSet 2 ≅ Pₐ`
(`annulusBaseDiffeomorph`, by `IsSmoothEmbedding.diffeomorphOfRangeEq`) carrying the planar
boundary circles to those of `Pₐ`. Pushing a planar collar `κ` through it and the trivialization
gives a half collar `annulusPieceCollar P κ` of the piece. The pushed long collar of the port `nf`
agrees on the torus with the collar of the presentation at that port, and the pushed short collar
of the other port `nn` with the collar at `nn`. Straightening twice
(`exists_torusCollar_straightening`, in the piece as a compact carrier, supported in the disjoint
open sets of depth `< 5/4` about either torus) gives `exists_annulus_longCollar`: a half collar
`Λ` of the piece on `T² × [0, 10)` which is the presentation collar of `nf` near `0`, the
presentation collar of `nn` read backwards (circle coordinate inverted) near `10`, and whose image
together with the torus of `nn` is the whole piece.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

theorem planarCenter_two (n : Fin 2) : planarCenter 2 n = 0 := by
  simp [planarCenter]

def annulusDepth (n : Fin 2) (z : ℂ) : ℝ :=
  planarSign n * (‖z - planarCenter 2 n‖ - planarRadius n)

theorem annulusDepth_eq (n : Fin 2) (z : ℂ) :
    annulusDepth n z = planarSign n * (‖z‖ - planarRadius n) := by
  rw [annulusDepth, planarCenter_two, Complex.ofReal_zero, sub_zero]

theorem annulusDepth_add (z : ℂ) : annulusDepth 0 z + annulusDepth 1 z = 5 / 2 := by
  rw [annulusDepth_eq, annulusDepth_eq]
  simp only [planarSign, planarRadius, Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero]
  ring

theorem annulusDepth_add_rev {n n' : Fin 2} (h : n ≠ n') (z : ℂ) :
    annulusDepth n z + annulusDepth n' z = 5 / 2 := by
  fin_cases n <;> fin_cases n'
  · exact absurd rfl h
  · exact annulusDepth_add z
  · rw [add_comm]
    exact annulusDepth_add z
  · exact absurd rfl h

theorem annulusRadius_pos (n : Fin 2) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 10) :
    0 < planarRadius n + planarSign n * s / 4 := by
  fin_cases n <;> simp [planarRadius, planarSign] <;> linarith

theorem norm_annulusFormula (n : Fin 2) (t : Circle) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 10) :
    ‖planarCollarFormula 2 n ((t : ℂ), s) - planarCenter 2 n‖ =
      planarRadius n + planarSign n * s / 4 := by
  rw [planarCollarFormula_sub, norm_smul, norm_planarTwist, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (annulusRadius_pos n hs0 hs1).le]

theorem annulusDepth_formula (n : Fin 2) (t : Circle) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 10) :
    annulusDepth n (planarCollarFormula 2 n ((t : ℂ), s)) = s / 4 := by
  rw [annulusDepth, norm_annulusFormula n t hs0 hs1]
  have := planarSign_mul_self n
  linear_combination (s / 4) * this

theorem annulusFormula_mem (n : Fin 2) (t : Circle) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 10) :
    planarCollarFormula 2 n ((t : ℂ), s) ∈ planarModel 2 := by
  have h := norm_annulusFormula n t hs0 hs1
  rw [planarCenter_two, Complex.ofReal_zero, sub_zero] at h
  rw [mem_planarModel_two, h]
  fin_cases n <;> simp [planarRadius, planarSign] <;> constructor <;> linarith

theorem annulusDepth_nonneg (n : Fin 2) {z : ℂ} (hz : z ∈ planarModel 2) :
    0 ≤ annulusDepth n z :=
  planarSign_mul_nonneg n hz

theorem planarSet_two_ne_zero (n : Fin 2) (x : planarSet.{u} 2) :
    x.val.down - planarCenter 2 n ≠ 0 := by
  have hz := (mem_planarSet_iff (Or.inl rfl) x.val).mp x.2
  rw [mem_planarModel_two] at hz
  rw [planarCenter_two, Complex.ofReal_zero, sub_zero, ← norm_pos_iff]
  linarith [hz.2]

def annulusLongMap (n : Fin 2) (p : Circle × EuclideanHalfSpace 1) : planarSet.{u} 2 :=
  ⟨ULift.up (planarCollarFormula 2 n ((p.1 : ℂ), min (p.2.val 0) 10)),
    (mem_planarSet_iff (Or.inl rfl) _).mpr
      (annulusFormula_mem n p.1 (le_min p.2.2 (by norm_num)) (min_le_right _ _))⟩

def annulusLongTarget (n : Fin 2) : Set (planarSet.{u} 2) :=
  {x | annulusDepth n x.val.down < 10 / 4}

theorem annulusLongMap_val (n : Fin 2) {p : Circle × EuclideanHalfSpace 1}
    (hp : p.2.val 0 < 10) :
    (annulusLongMap.{u} n p).val.down = planarCollarFormula 2 n ((p.1 : ℂ), p.2.val 0) := by
  change planarCollarFormula 2 n ((p.1 : ℂ), min (p.2.val 0) 10) = _
  rw [min_eq_left hp.le]

def annulusLongCollar (n : Fin 2) :
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} 2) ∞ where
  toFun := annulusLongMap.{u} n
  invFun := planarCollarInv.{u} 2 n
  source := {p | p.2.val 0 < 10}
  target := annulusLongTarget n
  map_source' := by
    intro p hp
    have hp' : p.2.val 0 < 10 := hp
    change annulusDepth n (annulusLongMap.{u} n p).val.down < 10 / 4
    rw [annulusLongMap_val n hp', annulusDepth_formula n p.1 p.2.2 hp'.le]
    linarith
  map_target' := by
    intro x hx
    have hx' : annulusDepth n x.val.down < 10 / 4 := hx
    change max (4 * (planarSign n * (‖x.val.down - planarCenter 2 n‖ - planarRadius n))) 0 < 10
    exact max_lt (by unfold annulusDepth at hx'; linarith) (by norm_num)
  left_inv' := by
    intro p hp
    have hp' : p.2.val 0 < 10 := hp
    have hs0 := p.2.2
    change planarCollarInv.{u} 2 n (annulusLongMap.{u} n p) = p
    have hd := annulusDepth_formula n p.1 hs0 hp'.le
    unfold annulusDepth at hd
    unfold planarCollarInv
    rw [annulusLongMap_val n hp', hd, planarCollarFormula_sub, planarTwist_smul,
      planarTwist_planarTwist, unitOf_smul (annulusRadius_pos n hs0 hp'.le),
      show 4 * (p.2.val 0 / 4) = p.2.val 0 by ring, halfSpaceOneLift_coord]
  right_inv' := by
    intro x hx
    have hx' : annulusDepth n x.val.down < 10 / 4 := hx
    have hz := (mem_planarSet_iff (Or.inl rfl) x.val).mp x.2
    have h0 := planarSign_mul_nonneg n hz
    set v := 4 * (planarSign n * (‖x.val.down - planarCenter 2 n‖ - planarRadius n)) with hv
    have hv0 : 0 ≤ v := by rw [hv]; positivity
    have hv1 : v < 10 := by rw [hv]; unfold annulusDepth at hx'; linarith
    have hsrc : (planarCollarInv.{u} 2 n x).2.val 0 < 10 := by
      change max v 0 < 10
      exact max_lt hv1 (by norm_num)
    apply Subtype.ext
    apply ULift.ext
    rw [annulusLongMap_val n hsrc]
    change planarCollarFormula 2 n ((unitOf (planarTwist n (x.val.down - planarCenter 2 n)) : ℂ),
      max v 0) = x.val.down
    rw [max_eq_left hv0]
    unfold planarCollarFormula
    have hr : planarRadius n + planarSign n * v / 4 = ‖x.val.down - planarCenter 2 n‖ := by
      rw [hv]
      linear_combination (‖x.val.down - planarCenter 2 n‖ - planarRadius n) *
        planarSign_mul_self n
    simp only
    rw [hr, ← norm_planarTwist n, ← planarTwist_smul, norm_smul_unitOf, planarTwist_planarTwist,
      add_sub_cancel]
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_lt (continuous_const.mul (((continuous_norm.comp
    ((contMDiff_planarSet_down 2).continuous.sub continuous_const))).sub continuous_const))
    continuous_const
  contMDiffOn_toFun := by
    refine ((planarAtlas 2).contMDiffOn_iff_subtype_val _ _).mpr ?_
    have hpair : ContMDiff circleCollarModel 𝓘(ℝ, ℂ × ℝ) ∞
        (fun p : Circle × EuclideanHalfSpace 1 => ((p.1 : ℂ), p.2.val 0)) :=
      (contMDiff_circle_coe.comp contMDiff_fst).prodMk_space
        (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
    have h := contMDiff_planeLift_up.{u}.comp
      ((contDiff_planarCollarFormula 2 n).contMDiff.comp hpair)
    refine h.contMDiffOn.congr fun p hp => ?_
    change ULift.up (annulusLongMap.{u} n p).val.down = _
    rw [annulusLongMap_val n hp]
    rfl
  contMDiffOn_invFun := by
    have hD : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
        (fun x : planarSet.{u} 2 => x.val.down - planarCenter 2 n) :=
      (contDiff_id.sub contDiff_const).contMDiff.comp (contMDiff_planarSet_down 2)
    have hfirst : ContMDiffOn (𝓡∂ 2) (𝓡 1) ∞
        (fun x : planarSet.{u} 2 => unitOf (planarTwist n (x.val.down - planarCenter 2 n)))
        (annulusLongTarget n) :=
      contMDiffOn_unitOf.comp ((contDiff_planarTwist n).contMDiff.comp hD).contMDiffOn
        fun x _ => by
          change planarTwist n _ ≠ 0
          rw [← norm_pos_iff, norm_planarTwist, norm_pos_iff]
          exact planarSet_two_ne_zero n x
    have hnorm : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
        (fun x : planarSet.{u} 2 =>
          4 * (planarSign n * (‖x.val.down - planarCenter 2 n‖ - planarRadius n)))
        (annulusLongTarget n) := by
      intro x _
      have hn : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
          (fun x : planarSet.{u} 2 => ‖x.val.down - planarCenter 2 n‖) x :=
        (contDiffAt_norm ℝ (planarSet_two_ne_zero n x)).contMDiffAt.comp x (hD x)
      exact ((contDiff_const.mul (contDiff_const.mul (contDiff_id.sub contDiff_const))).contMDiff
        |>.contMDiffAt.comp x hn).contMDiffWithinAt
    have hsecond : ContMDiffOn (𝓡∂ 2) (𝓡∂ 1) ∞
        (fun x : planarSet.{u} 2 => Manifold.halfSpaceOneLift
          (4 * (planarSign n * (‖x.val.down - planarCenter 2 n‖ - planarRadius n))))
        (annulusLongTarget n) :=
      Manifold.contMDiffOn_halfSpaceOneLift.comp hnorm fun x _ => by
        have := planarSign_mul_nonneg n ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.2)
        change (0 : ℝ) ≤ _
        positivity
    exact hfirst.prodMk hsecond

theorem annulusLongCollar_source (n : Fin 2) (p : Circle × EuclideanHalfSpace 1) :
    p ∈ (annulusLongCollar.{u} n).source ↔ p.2.val 0 < 10 := Iff.rfl

theorem annulusLongCollar_target (n : Fin 2) (x : planarSet.{u} 2) :
    x ∈ (annulusLongCollar.{u} n).target ↔ annulusDepth n x.val.down < 10 / 4 := Iff.rfl

theorem annulusLongCollar_apply_val (n : Fin 2) {p : Circle × EuclideanHalfSpace 1}
    (hp : p.2.val 0 < 10) :
    (annulusLongCollar.{u} n p).val.down = planarCollarFormula 2 n ((p.1 : ℂ), p.2.val 0) :=
  annulusLongMap_val n hp

theorem annulusDepth_annulusLongCollar (n : Fin 2) {p : Circle × EuclideanHalfSpace 1}
    (hp : p.2.val 0 < 10) :
    annulusDepth n (annulusLongCollar.{u} n p).val.down = p.2.val 0 / 4 := by
  rw [annulusLongCollar_apply_val n hp, annulusDepth_formula n p.1 p.2.2 hp.le]

theorem annulusDepth_planarCollar (n : Fin 2) {p : Circle × EuclideanHalfSpace 1}
    (hp : p ∈ circleCollarSource) :
    annulusDepth n (planarCollar.{u} 2 (Or.inl rfl) n p).val.down = p.2.val 0 / 4 := by
  have hp' : p.2.val 0 < 1 := hp
  rw [planarCollar_apply_val (Or.inl rfl) n hp, annulusDepth_formula n p.1 p.2.2 (by linarith)]

theorem annulusLongCollar_eq_planarCollar (n : Fin 2) {p : Circle × EuclideanHalfSpace 1}
    (hp : p ∈ circleCollarSource) :
    annulusLongCollar.{u} n p = planarCollar.{u} 2 (Or.inl rfl) n p := by
  have hp' : p.2.val 0 < 1 := hp
  apply Subtype.ext
  apply ULift.ext
  rw [annulusLongCollar_apply_val n (by linarith), planarCollar_apply_val (Or.inl rfl) n hp]

theorem annulusLongCollar_near_end {n n' : Fin 2} (h : n ≠ n') (t : Circle) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    annulusLongCollar.{u} n (t, Manifold.halfSpaceOneLift (10 - s)) =
      planarCollar.{u} 2 (Or.inl rfl) n' (t⁻¹, Manifold.halfSpaceOneLift s) := by
  have hl : (Manifold.halfSpaceOneLift (10 - s)).val 0 = 10 - s := by
    change max (10 - s) 0 = 10 - s
    exact max_eq_left (by linarith)
  have hl' : (Manifold.halfSpaceOneLift s).val 0 = s := by
    change max s 0 = s
    exact max_eq_left hs0
  have hsrc : (t⁻¹, Manifold.halfSpaceOneLift s) ∈ circleCollarSource := by
    change (Manifold.halfSpaceOneLift s).val 0 < 1
    rw [hl']
    exact hs1
  apply Subtype.ext
  apply ULift.ext
  change planarCollarFormula 2 n (((t : ℂ)), min ((Manifold.halfSpaceOneLift (10 - s)).val 0) 10) =
    (planarCollar.{u} 2 (Or.inl rfl) n' (t⁻¹, Manifold.halfSpaceOneLift s)).val.down
  rw [planarCollar_apply_val (Or.inl rfl) n' hsrc, hl, min_eq_left (by linarith), hl']
  rw [Circle.coe_inv_eq_conj]
  fin_cases n <;> fin_cases n'
  · exact absurd rfl h
  · simp [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist,
      Complex.real_smul]
    ring
  · simp [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist,
      Complex.real_smul]
    ring
  · exact absurd rfl h

theorem annulusLongCollar_or {n n' : Fin 2} (h : n ≠ n') (x : planarSet.{u} 2) :
    x ∈ (annulusLongCollar.{u} n).target ∨
      ∃ t, x = planarCollar.{u} 2 (Or.inl rfl) n' (t, halfZero) := by
  by_cases hx : annulusDepth n x.val.down < 10 / 4
  · exact Or.inl hx
  · right
    have hz := (mem_planarSet_iff (Or.inl rfl) x.val).mp x.2
    have hadd := annulusDepth_add_rev h x.val.down
    have h0 := annulusDepth_nonneg n' hz
    have hd : annulusDepth n' x.val.down = 0 := by linarith [not_lt.mp hx]
    have hxt : x ∈ (planarCollar.{u} 2 (Or.inl rfl) n').target := by
      change annulusDepth n' x.val.down < 1 / 4
      rw [hd]
      norm_num
    refine ⟨((planarCollar.{u} 2 (Or.inl rfl) n').symm x).1, ?_⟩
    have hinv := (planarCollar.{u} 2 (Or.inl rfl) n').right_inv' hxt
    have h2 : (planarCollar.{u} 2 (Or.inl rfl) n').symm x =
        (((planarCollar.{u} 2 (Or.inl rfl) n').symm x).1, halfZero) := by
      refine Prod.ext rfl ?_
      change Manifold.halfSpaceOneLift (4 * annulusDepth n' x.val.down) = halfZero
      rw [hd, mul_zero, ← halfPoint_eq_halfSpaceOneLift 0 le_rfl]
      rfl
    change (planarCollar.{u} 2 (Or.inl rfl) n') ((planarCollar.{u} 2 (Or.inl rfl) n').symm x) =
      x at hinv
    rw [h2] at hinv
    exact hinv.symm

def torusCollarSwap :
    (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, circleCollarModel.prod (𝓡 1)⟯
    ((Circle × EuclideanHalfSpace 1) × Circle) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)

def torusInvFirst : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus where
  toFun p := (p.1⁻¹, p.2)
  invFun p := (p.1⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_fst).prodMk contMDiff_snd

theorem torusInvFirst_apply (p : Torus) : torusInvFirst p = (p.1⁻¹, p.2) := rfl

section Product

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}

def annulusBaseDiffeomorph (P : ProductFibredPiece T i 2) :
    planarSet.{u} 2 ≃ₘ⟮𝓡∂ 2, SurfaceModel.model P.base.surface.kind⟯ P.base.surface.Carrier :=
  (planarBase.{u} 2 (Or.inl rfl)).isSmoothEmbedding.diffeomorphOfRangeEq P.base.isSmoothEmbedding
    (by rw [(planarBase.{u} 2 (Or.inl rfl)).range_embedding, P.base.range_embedding])

theorem embedding_annulusBaseDiffeomorph (P : ProductFibredPiece T i 2) (y : planarSet.{u} 2) :
    P.base.embedding (annulusBaseDiffeomorph P y) = y.val.down :=
  (planarBase.{u} 2 (Or.inl rfl)).isSmoothEmbedding.comp_diffeomorphOfRangeEq
    P.base.isSmoothEmbedding _ y

theorem annulusBaseDiffeomorph_collar (P : ProductFibredPiece T i 2) (n : Fin 2) (t : Circle) :
    annulusBaseDiffeomorph P (planarCollar.{u} 2 (Or.inl rfl) n (t, halfZero)) =
      P.base.collar n (t, halfZero) := by
  apply P.base.isSmoothEmbedding.isEmbedding.injective
  rw [embedding_annulusBaseDiffeomorph, P.base.embedding_collar, planarCollar_zero_val]

def annulusPieceCollar (P : ProductFibredPiece T i 2)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} 2) ∞) :
    PartialDiffeomorph halfCollarModel T.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (T.components.piece i) ∞ :=
  (torusCollarSwap.toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.prod κ
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph)).trans
    (((annulusBaseDiffeomorph P).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
      P.trivialization).toPartialDiffeomorph

theorem annulusPieceCollar_apply (P : ProductFibredPiece T i 2)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} 2) ∞) (p : Torus × EuclideanHalfSpace 1) :
    annulusPieceCollar P κ p =
      P.trivialization (annulusBaseDiffeomorph P (κ (p.1.1, p.2)), p.1.2) :=
  rfl

theorem annulusPieceCollar_source (P : ProductFibredPiece T i 2)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} 2) ∞) (p : Torus × EuclideanHalfSpace 1) :
    p ∈ (annulusPieceCollar P κ).source ↔ (p.1.1, p.2) ∈ κ.source :=
  ⟨fun h => h.1.2.1, fun h => ⟨⟨trivial, h, trivial⟩, trivial⟩⟩

def productDepth (P : ProductFibredPiece T i 2) (n : Fin 2) (x : T.components.piece i) : ℝ :=
  annulusDepth n ((annulusBaseDiffeomorph P).symm (P.trivialization.symm x).1).val.down

theorem continuous_productDepth (P : ProductFibredPiece T i 2) (n : Fin 2) :
    Continuous (productDepth P n) := by
  have h1 : Continuous fun x : T.components.piece i =>
      ((annulusBaseDiffeomorph P).symm (P.trivialization.symm x).1).val.down :=
    (contMDiff_planarSet_down 2).continuous.comp ((annulusBaseDiffeomorph P).symm.continuous.comp
      (continuous_fst.comp P.trivialization.symm.continuous))
  exact continuous_const.mul (((continuous_norm.comp (h1.sub continuous_const))).sub
    continuous_const)

theorem productDepth_annulusPieceCollar (P : ProductFibredPiece T i 2) (n : Fin 2)
    (κ : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} 2) ∞) (p : Torus × EuclideanHalfSpace 1) :
    productDepth P n (annulusPieceCollar P κ p) = annulusDepth n (κ (p.1.1, p.2)).val.down := by
  rw [productDepth, annulusPieceCollar_apply, Diffeomorph.symm_apply_apply,
    Diffeomorph.symm_apply_apply]

theorem productDepth_add (P : ProductFibredPiece T i 2) {n n' : Fin 2} (h : n ≠ n')
    (x : T.components.piece i) : productDepth P n x + productDepth P n' x = 5 / 2 :=
  annulusDepth_add_rev h _

theorem pieceCollar_zero_isBoundaryPoint (s : T.OwnedSide i) (t : Torus) :
    T.cutCarrier.model.IsBoundaryPoint (T.pieceCollar i s (t, halfZero)) := by
  refine (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := T.cutCarrier.model)
    (u := T.components.piece i)).mpr ?_
  rw [T.pieceCollar_apply i s (zero_mem_halfCollarSource t)]
  exact (T.sideCollar_zero_mem s.val t).1

theorem annulusPieceCollar_planarCollar_zero (P : ProductFibredPiece T i 2) (n : Fin 2)
    (t : Torus) :
    annulusPieceCollar P (planarCollar.{u} 2 (Or.inl rfl) n) (t, halfZero) =
      T.pieceCollar i (P.port n) (t, halfZero) := by
  rw [P.collar_eq n (t, halfZero) (zero_mem_halfCollarSource t), annulusPieceCollar_apply,
    annulusBaseDiffeomorph_collar]

theorem annulusPieceCollar_annulusLongCollar_zero (P : ProductFibredPiece T i 2) (n : Fin 2)
    (t : Torus) : annulusPieceCollar P (annulusLongCollar.{u} n) (t, halfZero) =
      T.pieceCollar i (P.port n) (t, halfZero) := by
  rw [← annulusPieceCollar_planarCollar_zero P n t, annulusPieceCollar_apply,
    annulusPieceCollar_apply,
    annulusLongCollar_eq_planarCollar n (halfZero_mem_circleCollarSource t.1)]

theorem exists_piece_straightening
    (c₀ c₁ : PartialDiffeomorph halfCollarModel T.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (T.components.piece i) ∞)
    (hsrc : ∀ p, (p, halfZero) ∈ c₀.source ∩ c₁.source)
    (h₀ : ∀ p, c₀ (p, halfZero) = c₁ (p, halfZero))
    (hb : ∀ p, T.cutCarrier.model.IsBoundaryPoint (c₀ (p, halfZero)))
    {O : Set (T.components.piece i)} (hO : IsOpen O)
    (hK : range (fun p => c₀ (p, halfZero)) ⊆ O) :
    ∃ δ > 0, ∃ Φ : (T.components.piece i) ≃ₘ⟮T.cutCarrier.model, T.cutCarrier.model⟯
      (T.components.piece i),
      (∀ p t, t.1 0 < δ → Φ (c₀ (p, t)) = c₁ (p, t)) ∧ EqOn Φ id Oᶜ :=
  exists_torusCollar_straightening (C := GC.Topology.componentCarrier T.cutCarrier T.components i)
    c₀ c₁ hsrc h₀ hb hO hK

private theorem diffeo_symm_fix {Φ : (T.components.piece i) ≃ₘ⟮T.cutCarrier.model,
    T.cutCarrier.model⟯ (T.components.piece i)} {O : Set (T.components.piece i)}
    (hΦ : EqOn Φ id Oᶜ) {x : T.components.piece i} (hx : x ∉ O) : Φ.symm x = x := by
  have h : Φ x = x := hΦ hx
  calc Φ.symm x = Φ.symm (Φ x) := by rw [h]
    _ = x := Φ.symm_apply_apply x

private theorem diffeo_symm_mem {Φ : (T.components.piece i) ≃ₘ⟮T.cutCarrier.model,
    T.cutCarrier.model⟯ (T.components.piece i)} {O : Set (T.components.piece i)}
    (hΦ : EqOn Φ id Oᶜ) {y : T.components.piece i} (hy : y ∈ O) : Φ.symm y ∈ O := by
  by_contra h
  have h1 : Φ (Φ.symm y) = Φ.symm y := hΦ h
  rw [Φ.apply_symm_apply] at h1
  exact h (h1 ▸ hy)

theorem exists_annulus_longCollar (P : ProductFibredPiece T i 2) {nf nn : Fin 2}
    (hne : nf ≠ nn) :
    ∃ Λ : PartialDiffeomorph halfCollarModel T.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (T.components.piece i) ∞, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ p, p ∈ Λ.source ↔ p.2.val 0 < 10) ∧
      (∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < δ → Λ p = T.pieceCollar i (P.port nf) p) ∧
      (∀ (t : Torus) (u : ℝ), 10 - δ < u → u < 10 →
        Λ (t, Manifold.halfSpaceOneLift u) =
          T.pieceCollar i (P.port nn) (torusInvFirst t, Manifold.halfSpaceOneLift (10 - u))) ∧
      ∀ x, x ∈ Λ.target ∨ ∃ t, x = T.pieceCollar i (P.port nn) (t, halfZero) := by
  classical
  set Λ₀ := annulusPieceCollar P (annulusLongCollar.{u} nf) with hΛ₀
  set c₁ := annulusPieceCollar P (planarCollar.{u} 2 (Or.inl rfl) nn) with hc₁
  set cf := T.pieceCollar i (P.port nf) with hcf
  set cn := T.pieceCollar i (P.port nn) with hcn
  let O : Fin 2 → Set (T.components.piece i) := fun n => {x | productDepth P n x < 5 / 4}
  have hO : ∀ n, IsOpen (O n) := fun n =>
    isOpen_lt (continuous_productDepth P n) continuous_const
  have hOdisj : ∀ x, x ∈ O nf → x ∉ O nn := by
    intro x h1 h2
    have h1' : productDepth P nf x < 5 / 4 := h1
    have h2' : productDepth P nn x < 5 / 4 := h2
    have := productDepth_add P hne x
    linarith
  have hdΛ : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 10 →
      productDepth P nf (Λ₀ p) = p.2.val 0 / 4 := fun p hp => by
    rw [productDepth_annulusPieceCollar]
    exact annulusDepth_annulusLongCollar nf hp
  have hdc : ∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < 1 →
      productDepth P nn (c₁ p) = p.2.val 0 / 4 := fun p hp => by
    rw [productDepth_annulusPieceCollar]
    exact annulusDepth_planarCollar nn hp
  have hzf : ∀ t, cf (t, halfZero) = Λ₀ (t, halfZero) := fun t =>
    (annulusPieceCollar_annulusLongCollar_zero P nf t).symm
  have hzn : ∀ t, cn (t, halfZero) = c₁ (t, halfZero) := fun t =>
    (annulusPieceCollar_planarCollar_zero P nn t).symm
  have hz0 : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := rfl
  obtain ⟨δf, hδf, Φf, hΦf, hΦfO⟩ := exists_piece_straightening cf Λ₀
    (fun t => ⟨(T.pieceCollar_source i _).symm ▸ zero_mem_halfCollarSource t,
      (annulusPieceCollar_source P _ _).mpr (by
        change (halfZero : EuclideanHalfSpace 1).val 0 < 10
        rw [hz0]
        norm_num)⟩)
    hzf (fun t => pieceCollar_zero_isBoundaryPoint _ t) (hO nf) (by
      rintro _ ⟨t, rfl⟩
      change productDepth P nf (cf (t, halfZero)) < 5 / 4
      rw [hzf, hdΛ _ (by rw [hz0]; norm_num)]
      change (halfZero : EuclideanHalfSpace 1).val 0 / 4 < 5 / 4
      rw [hz0]
      norm_num)
  obtain ⟨δn, hδn, Φn, hΦn, hΦnO⟩ := exists_piece_straightening cn c₁
    (fun t => ⟨(T.pieceCollar_source i _).symm ▸ zero_mem_halfCollarSource t,
      (annulusPieceCollar_source P _ _).mpr (halfZero_mem_circleCollarSource t.1)⟩)
    hzn (fun t => pieceCollar_zero_isBoundaryPoint _ t) (hO nn) (by
      rintro _ ⟨t, rfl⟩
      change productDepth P nn (cn (t, halfZero)) < 5 / 4
      rw [hzn, hdc _ (by rw [hz0]; norm_num)]
      change (halfZero : EuclideanHalfSpace 1).val 0 / 4 < 5 / 4
      rw [hz0]
      norm_num)
  let Λ := (Λ₀.trans Φf.symm.toPartialDiffeomorph).trans Φn.symm.toPartialDiffeomorph
  have hΛ : ∀ p, Λ p = Φn.symm (Φf.symm (Λ₀ p)) := fun p => rfl
  set δ := min (min δf δn) 1 with hδ
  have hδf' : δ ≤ δf := (min_le_left _ _).trans (min_le_left _ _)
  have hδn' : δ ≤ δn := (min_le_left _ _).trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  refine ⟨Λ, δ, lt_min (lt_min hδf hδn) one_pos, hδ1, fun p => ?_, fun p hp => ?_,
    fun t u hu1 hu2 => ?_, fun x => ?_⟩
  · constructor
    · intro h
      exact (annulusPieceCollar_source P _ p).mp h.1.1
    · intro h
      exact ⟨⟨(annulusPieceCollar_source P _ p).mpr h, trivial⟩, trivial⟩
  · have hpf : p.2.val 0 < δf := hp.trans_le hδf'
    have h1 : Φf (cf p) = Λ₀ p := hΦf p.1 p.2 hpf
    have h2 : Φf.symm (Λ₀ p) = cf p := by rw [← h1, Φf.symm_apply_apply]
    have hmem : Λ₀ p ∈ O nf := by
      change productDepth P nf (Λ₀ p) < 5 / 4
      rw [hdΛ p (by linarith)]
      linarith [p.2.2]
    have hmem' : cf p ∈ O nf := h2 ▸ diffeo_symm_mem hΦfO hmem
    rw [hΛ, h2, diffeo_symm_fix hΦnO (hOdisj _ hmem')]
  · obtain ⟨s, rfl⟩ : ∃ s, u = 10 - s := ⟨10 - u, by ring⟩
    have hs0 : 0 < s := by linarith
    have hs1 : s < δ := by linarith
    rw [show (10 : ℝ) - (10 - s) = s by ring]
    have hl : (Manifold.halfSpaceOneLift s).val 0 = s := by
      change max s 0 = s
      exact max_eq_left hs0.le
    have hend : Λ₀ (t, Manifold.halfSpaceOneLift (10 - s)) =
        c₁ (torusInvFirst t, Manifold.halfSpaceOneLift s) := by
      rw [annulusPieceCollar_apply, annulusPieceCollar_apply,
        annulusLongCollar_near_end hne t.1 hs0.le (by linarith)]
      rfl
    have hsrc1 : (torusInvFirst t, Manifold.halfSpaceOneLift s).2.val 0 < 1 := by
      change (Manifold.halfSpaceOneLift s).val 0 < 1
      rw [hl]
      linarith
    have hmem : c₁ (torusInvFirst t, Manifold.halfSpaceOneLift s) ∈ O nn := by
      change productDepth P nn _ < 5 / 4
      rw [hdc _ hsrc1]
      change (Manifold.halfSpaceOneLift s).val 0 / 4 < 5 / 4
      rw [hl]
      linarith
    have hnf : c₁ (torusInvFirst t, Manifold.halfSpaceOneLift s) ∉ O nf := fun h =>
      hOdisj _ h hmem
    have h1 : Φn (cn (torusInvFirst t, Manifold.halfSpaceOneLift s)) =
        c₁ (torusInvFirst t, Manifold.halfSpaceOneLift s) :=
      hΦn _ _ (by rw [hl]; linarith)
    rw [hΛ, hend, diffeo_symm_fix hΦfO hnf, ← h1, Φn.symm_apply_apply]
  · set x' := Φf (Φn x) with hx'
    set b := (annulusBaseDiffeomorph P).symm (P.trivialization.symm x').1 with hb
    rcases annulusLongCollar_or.{u} hne b with hbt | ⟨t, ht⟩
    · left
      set q := (annulusLongCollar.{u} nf).symm b with hq
      have hqs : q ∈ (annulusLongCollar.{u} nf).source := (annulusLongCollar nf).map_target' hbt
      let p : Torus × EuclideanHalfSpace 1 := ((q.1, (P.trivialization.symm x').2), q.2)
      have hps : p ∈ Λ.source := ⟨⟨(annulusPieceCollar_source P _ p).mpr hqs, trivial⟩, trivial⟩
      have hΛ₀p : Λ₀ p = x' := by
        rw [annulusPieceCollar_apply]
        change P.trivialization (annulusBaseDiffeomorph P
          ((annulusLongCollar.{u} nf) ((annulusLongCollar.{u} nf).symm b)),
            (P.trivialization.symm x').2) = x'
        rw [PartialDiffeomorph.apply_symm_apply _ hbt, hb, Diffeomorph.apply_symm_apply]
        exact P.trivialization.apply_symm_apply x'
      have hΛp : Λ p = x := by
        rw [hΛ, hΛ₀p, hx', Φf.symm_apply_apply, Φn.symm_apply_apply]
      rw [← hΛp]
      exact Λ.map_source' hps
    · right
      set θ := (P.trivialization.symm x').2
      have hx'n : x' = cn ((t, θ), halfZero) := by
        rw [hzn, annulusPieceCollar_apply]
        change x' = P.trivialization (annulusBaseDiffeomorph P
          (planarCollar.{u} 2 (Or.inl rfl) nn (t, halfZero)), θ)
        rw [← ht, hb, Diffeomorph.apply_symm_apply]
        exact (P.trivialization.apply_symm_apply x').symm
      have hfixn : Φn (cn ((t, θ), halfZero)) = cn ((t, θ), halfZero) := by
        rw [hΦn _ _ (by rw [hz0]; exact hδn)]
        exact (hzn _).symm
      have hmemn : cn ((t, θ), halfZero) ∈ O nn := by
        change productDepth P nn _ < 5 / 4
        rw [hzn, hdc _ (by rw [hz0]; norm_num), hz0]
        norm_num
      have hfixf : Φf.symm (cn ((t, θ), halfZero)) = cn ((t, θ), halfZero) :=
        diffeo_symm_fix hΦfO (fun h => hOdisj _ h hmemn)
      refine ⟨(t, θ), ?_⟩
      have h1 : Φn x = cn ((t, θ), halfZero) := by
        rw [← Φf.symm_apply_apply (Φn x), ← hx', hx'n, hfixf]
      rw [← Φn.symm_apply_apply x, h1, ← hfixn, Φn.symm_apply_apply, hfixn]

end Product

end GC.Seifert
