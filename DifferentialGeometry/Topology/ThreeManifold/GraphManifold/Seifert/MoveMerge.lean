import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorb
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPants

/-!
# The merge move M1 of the (S⁺) normalization

Lane N1, for `MoveMerge` of `Seifert/Normalize.lean`: a solid torus `V = seamPiece j b` on a
seam `j` whose host `H = hostPiece j b` has kind `k ≥ 2`, at filling distance `1`.

Tier 1 (slopes and model). The host coordinates of the meridian of `V` form a section slope
`(1, q)` exactly when the distance is `1` (`Merge.exists_eq_sectionSlope`,
`IsMergeSeam.exists_mergeSlope_eq`). The fibre shear `fibreShear m = !![1, 0; m, 1]` fixes the
fibre, moves `(1, q)` to `(1, q + m)` and is the matrix of the fibre-preserving torus twist
`fibreTwist m (u, v) = (u, u ^ m v)`; the host fibre is a longitude of `V`
(`IsMergeSeam.delta_solidFibreSlope`). The model is K06c at `p = 1`, `a = 0`
(`sectionFilling q`): `mergeModel q` is an elementary presentation (pants and solid torus) with
a merge seam, its filled carrier is the product of the filled base with the circle
(`filledSet_sectionFilling`: the cone point does not depend on the fibre), and the pants enters
this product by `(ζ, λ) ↦ (ζ, unitOf (ζ - 3/2) ^ q λ)` (`modelProduct_coneLift`). So the
remaining ports keep their tori and fibres, but their sections change by fibre twists of total
degree `q` (the relative Euler number): the port data are unchanged only up to reparametrizing
the ports, which is why tier 3 retwists.

Tier 2 (surgery). If the host has no self-seam (`HostSelfSeamFree`), `j` is the only seam
inside `seamPair j` (`IsMergeSeam.eq_of_internal`), and P2a's `contract` along it, with the side
conditions of `Seifert/MoveAbsorb.lean`, is `mergeContraction`: one seam fewer
(`mergeContraction_pairing_count`), one piece fewer, the seams other than `j` with the same
charts and matchings (`mergeSeamEquiv`, `mergeContraction_seam`, `mergeContraction_matching`),
and a merged piece `mergeLast` owning `k - 1` sides (`mergeContraction_card_ownedSide_last`).

Tier 3. `TorusPresentation.retwist σL σR` reparametrizes the seam sides by torus
diffeomorphisms: parameters and collars are precomposed, matchings conjugated, seam charts
precomposed on the left side, and the boundary reversal is transported by
`Merge.reverses_twist`. A `TwistedProductPiece` is a `ProductFibredPiece` up to such a
reparametrization of its ports and becomes one after retwisting (`toProduct`). The product
pieces off the merged piece survive the contraction (`ProductFibredPiece.contractTransport`,
through `contractPieceDiffeomorph` and `contractOwnedSideEquiv`) and the retwist
(`retwistOther`). So a twisted product structure over `Pₖ₋₁` on the merged piece gives an
elementary presentation with one seam fewer (`exists_of_twistedProductPiece`). If the host has
a self-seam, `V ∪ H` meets no crossing seam, so it is the whole closed carrier: two pieces,
`k = 3` and two seams (`components_count_of_selfSeam`, `complexity_of_selfSeam`).

Two local lemmas are left as `sorry`. `exists_twistedProductPiece_merge`: filling `Pₖ × S¹`
along a section slope gives a product over `Pₖ₋₁` keeping the other collars up to torus
reparametrization; its proof uses that torus diffeomorphisms are isotopic to linear ones (the
input `TorusMappingClassLinear` of K08) and collar uniqueness. `exists_complexity_one_of_selfSeam`:
the two-piece self-seam configuration is a torus bundle, an annulus piece glued to itself.
`moveMerge` derives `MoveMerge` from them.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace Merge

theorem isPrimitive_one_left (q : ℤ) : IsPrimitive (1, q) := Int.gcd_one_left q

def sectionSlope (q : ℤ) : PrimitiveSlope := PrimitiveSlope.mk (1, q) (isPrimitive_one_left q)

theorem sectionSlope_zero : sectionSlope 0 = meridianSlope := rfl

theorem delta_sectionSlope_fiberSlope (q : ℤ) :
    PrimitiveSlope.delta (sectionSlope q) fiberSlope = 1 := by
  rw [sectionSlope, fiberSlope, PrimitiveSlope.delta_mk]
  simp [slopeDet]

theorem exists_eq_sectionSlope {a : PrimitiveSlope} (h : PrimitiveSlope.delta a fiberSlope = 1) :
    ∃ q, a = sectionSlope q := by
  induction a using PrimitiveSlope.ind with
  | h v hv =>
    rw [fiberSlope, PrimitiveSlope.delta_mk] at h
    simp only [slopeDet, mul_one, mul_zero, sub_zero] at h
    rcases Int.natAbs_eq_iff.mp h with h1 | h1
    · refine ⟨v.2, (PrimitiveSlope.mk_eq_mk_iff _ _).2 (Or.inl ?_)⟩
      exact Prod.ext h1.symm rfl
    · refine ⟨-v.2, (PrimitiveSlope.mk_eq_mk_iff _ _).2 (Or.inr ?_)⟩
      exact Prod.ext (by simp [h1]) (by simp)

def fibreShearMatrix (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; m, 1]

theorem det_fibreShearMatrix (m : ℤ) : (fibreShearMatrix m).det = 1 := by
  simp [fibreShearMatrix, Matrix.det_fin_two_of]

def fibreShear (m : ℤ) : GL (Fin 2) ℤ :=
  PrimitiveSlope.unitOfDet (fibreShearMatrix m) (Or.inl (det_fibreShearMatrix m))

theorem fibreShear_smul_fiberSlope (m : ℤ) : fibreShear m • fiberSlope = fiberSlope := by
  rw [fiberSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff]
  left
  simp [smulVec, fibreShear, PrimitiveSlope.val_unitOfDet, fibreShearMatrix]

theorem fibreShear_smul_sectionSlope (m q : ℤ) :
    fibreShear m • sectionSlope q = sectionSlope (q + m) := by
  rw [sectionSlope, sectionSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff]
  left
  simp [smulVec, fibreShear, PrimitiveSlope.val_unitOfDet, fibreShearMatrix, add_comm]

theorem delta_fibreShear_smul (m : ℤ) (a : PrimitiveSlope) :
    PrimitiveSlope.delta (fibreShear m • a) fiberSlope = PrimitiveSlope.delta a fiberSlope := by
  rw [← fibreShear_smul_fiberSlope m, PrimitiveSlope.delta_smul, fibreShear_smul_fiberSlope]

def fibreTwist (m : ℤ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  linearTorusDiffeomorph (fibreShear m)

theorem fibreTwist_apply (m : ℤ) (x : Torus) : fibreTwist m x = (x.1, x.1 ^ m * x.2) := by
  change linearTorusMap (fibreShearMatrix m) x = _
  simp [linearTorusMap, fibreShearMatrix]

theorem fibreTwist_fst (m : ℤ) (x : Torus) : (fibreTwist m x).1 = x.1 := by
  rw [fibreTwist_apply]

theorem torusUnit_fibreTwist (m : ℤ) : torusUnit (fibreTwist m) = fibreShear m :=
  Units.ext (torusMatrix_linearTorusDiffeomorph (fibreShear m))

end Merge

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

def mergeSlope (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) :
    Bool → PrimitiveSlope
  | true => torusUnit (E.toTorus.pairing.matching j) • meridianSlope
  | false => (torusUnit (E.toTorus.pairing.matching j))⁻¹ • meridianSlope

def solidFibreSlope (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) :
    Bool → PrimitiveSlope
  | true => (torusUnit (E.toTorus.pairing.matching j))⁻¹ • fiberSlope
  | false => torusUnit (E.toTorus.pairing.matching j) • fiberSlope

theorem fillingDistance_eq_delta_mergeSlope (E : ElementaryPresentation W)
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    E.fillingDistance j b = PrimitiveSlope.delta (E.mergeSlope j b) fiberSlope := by
  cases b
  · exact E.fillingDistance_false j
  · rfl

theorem delta_solidFibreSlope_meridianSlope (E : ElementaryPresentation W)
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    PrimitiveSlope.delta (E.solidFibreSlope j b) meridianSlope = E.fillingDistance j b := by
  rw [E.fillingDistance_eq_delta_mergeSlope]
  cases b
  · change PrimitiveSlope.delta (torusUnit _ • fiberSlope) meridianSlope =
      PrimitiveSlope.delta ((torusUnit _)⁻¹ • meridianSlope) fiberSlope
    rw [← PrimitiveSlope.delta_smul (torusUnit (E.toTorus.pairing.matching j))⁻¹, inv_smul_smul,
      PrimitiveSlope.delta_comm]
  · change PrimitiveSlope.delta ((torusUnit _)⁻¹ • fiberSlope) meridianSlope =
      PrimitiveSlope.delta (torusUnit _ • meridianSlope) fiberSlope
    rw [← PrimitiveSlope.delta_smul (torusUnit (E.toTorus.pairing.matching j)), smul_inv_smul,
      PrimitiveSlope.delta_comm]

namespace IsMergeSeam

variable {E : ElementaryPresentation W} {j : Fin E.toTorus.pairing.count} {b : Bool}

theorem kind_seamPiece (h : E.IsMergeSeam j b) : E.kind (E.seamPiece j b) = 1 := h.1

theorem two_le_kind_hostPiece (h : E.IsMergeSeam j b) : 2 ≤ E.kind (E.hostPiece j b) := h.2.1

theorem seamPiece_ne_hostPiece (h : E.IsMergeSeam j b) : E.seamPiece j b ≠ E.hostPiece j b := by
  intro he
  have h1 := h.kind_seamPiece
  have h2 := h.two_le_kind_hostPiece
  rw [he] at h1
  omega

theorem exists_mergeSlope_eq (h : E.IsMergeSeam j b) :
    ∃ q, E.mergeSlope j b = Merge.sectionSlope q :=
  Merge.exists_eq_sectionSlope ((E.fillingDistance_eq_delta_mergeSlope j b).symm.trans h.2.2)

theorem exists_fibreShear_smul_mergeSlope (h : E.IsMergeSeam j b) :
    ∃ m, Merge.fibreShear m • E.mergeSlope j b = meridianSlope := by
  obtain ⟨q, hq⟩ := h.exists_mergeSlope_eq
  exact ⟨-q, by rw [hq, Merge.fibreShear_smul_sectionSlope, add_neg_cancel]; rfl⟩

theorem delta_solidFibreSlope (h : E.IsMergeSeam j b) :
    PrimitiveSlope.delta (E.solidFibreSlope j b) meridianSlope = 1 :=
  (E.delta_solidFibreSlope_meridianSlope j b).trans h.2.2

end IsMergeSeam

end ElementaryPresentation

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

def HostSelfSeamFree (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count)
    (b : Bool) : Prop :=
  ∀ k, E.toTorus.leftPiece k = E.hostPiece j b → E.toTorus.rightPiece k ≠ E.hostPiece j b

namespace IsMergeSeam

variable {E : ElementaryPresentation W} {j : Fin E.toTorus.pairing.count} {b : Bool}

theorem leftPiece_ne_rightPiece (h : E.IsMergeSeam j b) :
    E.toTorus.leftPiece j ≠ E.toTorus.rightPiece j := by
  have := h.seamPiece_ne_hostPiece
  cases b
  · exact this.symm
  · exact this

theorem eq_pairSide (h : E.IsMergeSeam j b) {s : E.toTorus.Side}
    (hs : E.toTorus.sidePiece s = E.seamPiece j b) : s = E.toTorus.pairSide j b := by
  have hc : Fintype.card (E.toTorus.OwnedSide (E.seamPiece j b)) ≤ 1 := by
    rw [E.card_ownedSide_eq_kind, h.1]
  exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨s, hs⟩ ⟨_, E.sidePiece_pairSide j b⟩)

theorem eq_of_internal (h : E.IsMergeSeam j b) (hf : E.HostSelfSeamFree j b)
    {k : Fin E.toTorus.pairing.count} (hl : E.toTorus.leftPiece k ∈ E.toTorus.seamPair j)
    (hr : E.toTorus.rightPiece k ∈ E.toTorus.seamPair j) : k = j := by
  rcases (E.mem_seamPair_iff j b _).mp hl with hl' | hl'
  · have he := h.eq_pairSide (s := .inl k) hl'
    cases b
    · exact absurd he (by simp [TorusPresentation.pairSide])
    · simpa [TorusPresentation.pairSide] using he
  rcases (E.mem_seamPair_iff j b _).mp hr with hr' | hr'
  · have he := h.eq_pairSide (s := .inr (.inl k)) hr'
    cases b
    · simpa [TorusPresentation.pairSide] using he
    · exact absurd he (by simp [TorusPresentation.pairSide])
  · exact absurd hr' (hf k hl')

theorem filter_internal (h : E.IsMergeSeam j b) (hf : E.HostSelfSeamFree j b) :
    (Finset.univ.filter fun k => E.toTorus.leftPiece k ∈ E.toTorus.seamPair j ∧
      E.toTorus.rightPiece k ∈ E.toTorus.seamPair j) = {j} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hr⟩
    exact h.eq_of_internal hf hl hr
  · rintro rfl
    exact ⟨E.toTorus.left_mem_seamPair k, E.toTorus.right_mem_seamPair k⟩

theorem isConnected_region (h : E.IsMergeSeam j b) (hf : E.HostSelfSeamFree j b)
    (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j) :
    IsConnected (Set.range (E.toTorus.restrictMap (E.toTorus.seamPair j)) \
      E.toTorus.crossingSurface (E.toTorus.seamPair j)) :=
  E.toTorus.isConnected_region_seamPair j (fun _ hl hr => h.eq_of_internal hf hl hr) hext

end IsMergeSeam

variable (E : ElementaryPresentation W)

def mergeContraction (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b)
    (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j) : TorusPresentation W :=
  E.toTorus.contract (E.toTorus.seamPair j) hext (E.toTorus.cutCarrier_kind_of_pos j.pos)
    (h.isConnected_region hf hext)

section Merge

variable (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
  (hf : E.HostSelfSeamFree j b) (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j)

theorem mergeContraction_pairing_count :
    (E.mergeContraction j b h hf hext).pairing.count + 1 = E.complexity := by
  rw [mergeContraction, TorusPresentation.contract_pairing_count, h.filter_internal hf,
    Finset.card_singleton]
  have := j.pos
  unfold complexity
  omega

theorem mergeContraction_components_count :
    (E.mergeContraction j b h hf hext).components.count + 1 = E.toTorus.components.count := by
  rw [mergeContraction, TorusPresentation.contract_components_count,
    TorusPresentation.seamPair, Finset.card_pair h.leftPiece_ne_rightPiece]
  have := Finset.card_le_univ ({E.toTorus.leftPiece j, E.toTorus.rightPiece j} :
    Finset (Fin E.toTorus.components.count))
  rw [Finset.card_pair h.leftPiece_ne_rightPiece, Fintype.card_fin] at this
  omega

def mergeLast : Fin (E.mergeContraction j b h hf hext).components.count :=
  E.toTorus.contractLast _ hext (E.toTorus.cutCarrier_kind_of_pos j.pos)
    (h.isConnected_region hf hext)

theorem mergeContraction_externalCount :
    (E.mergeContraction j b h hf hext).externalCount = E.toTorus.externalCount := rfl

theorem mergeContraction_seam (k : Fin (E.mergeContraction j b h hf hext).pairing.count) :
    (E.mergeContraction j b h hf hext).seam k =
      E.toTorus.seam (E.toTorus.nonInternal (E.toTorus.seamPair j) k).val := rfl

theorem mergeContraction_matching (k : Fin (E.mergeContraction j b h hf hext).pairing.count) :
    (E.mergeContraction j b h hf hext).pairing.matching k =
      E.toTorus.pairing.matching (E.toTorus.nonInternal (E.toTorus.seamPair j) k).val := rfl

def mergeSeamEquiv :
    Fin (E.mergeContraction j b h hf hext).pairing.count ≃
      {k : Fin E.toTorus.pairing.count // k ≠ j} :=
  (Fintype.equivFin (E.toTorus.NonInternal (E.toTorus.seamPair j))).symm.trans
    (Equiv.subtypeEquivRight fun k => ⟨fun hk e => hk (by
      rw [e]
      exact ⟨E.toTorus.left_mem_seamPair j, E.toTorus.right_mem_seamPair j⟩),
      fun hk hb => hk (h.eq_of_internal hf hb.1 hb.2)⟩)

theorem mergeSeamEquiv_val (k : Fin (E.mergeContraction j b h hf hext).pairing.count) :
    (E.mergeSeamEquiv j b h hf hext k).val =
      (E.toTorus.nonInternal (E.toTorus.seamPair j) k).val :=
  rfl

end Merge

end ElementaryPresentation

namespace Merge

def sectionFilling (q : ℤ) : ConeFilling where
  p := 1
  q := q
  a := 0
  b := 1
  one_le := le_rfl
  det_eq := by simp

theorem conePoint_sectionFilling (q : ℤ) (x : PlaneLift.{u} × Circle) :
    (sectionFilling q).conePoint x = ((3 / 2 : ℝ) : ℂ) + x.1.down / 6 := by
  simp only [ConeFilling.conePoint, sectionFilling, pow_one, neg_zero, zpow_zero,
    Circle.coe_one, mul_one]
  ring

theorem mem_filledSet_sectionFilling_iff (q : ℤ) (x : PlaneLift.{u} × Circle) :
    x ∈ (sectionFilling q).filledSet ↔
      ConeFilling.filledFunction (((3 / 2 : ℝ) : ℂ) + x.1.down / 6) ≤ 0 := by
  change ConeFilling.filledFunction ((sectionFilling q).conePoint x) ≤ 0 ↔ _
  rw [conePoint_sectionFilling]

theorem filledSet_sectionFilling (q : ℤ) :
    (sectionFilling q).filledSet.{u} =
      {z : PlaneLift.{u} | ConeFilling.filledFunction (((3 / 2 : ℝ) : ℂ) + z.down / 6) ≤ 0} ×ˢ
        Set.univ := by
  ext x
  rw [mem_filledSet_sectionFilling_iff]
  simp

theorem coneLift_snd_sectionFilling (q : ℤ) (x : PlaneLift.{u} × Circle) :
    ((sectionFilling q).coneLift x).2 = unitOf (x.1.down - ((3 / 2 : ℝ) : ℂ)) ^ q * x.2 := by
  simp [ConeFilling.coneLift, ConeFilling.coneTorus, ConeFilling.liftMatrix, linearTorusMap,
    sectionFilling]

def modelProduct (q : ℤ) (x : PlaneLift.{u} × Circle) : ℂ × Circle :=
  ((sectionFilling q).conePoint x, x.2)

theorem modelProduct_apply (q : ℤ) (x : PlaneLift.{u} × Circle) :
    modelProduct q x = (((3 / 2 : ℝ) : ℂ) + x.1.down / 6, x.2) := by
  rw [modelProduct, conePoint_sectionFilling]

theorem modelProduct_coneLift (q : ℤ) (x : PlaneLift.{u} × Circle)
    (hx : x.1.down ≠ ((3 / 2 : ℝ) : ℂ)) :
    modelProduct q ((sectionFilling q).coneLift x) =
      (x.1.down, unitOf (x.1.down - ((3 / 2 : ℝ) : ℂ)) ^ q * x.2) := by
  rw [modelProduct, (sectionFilling q).conePoint_coneLift x hx, coneLift_snd_sectionFilling]

def mergeModel (q : ℤ) : ElementaryPresentation (sectionFilling q).filledCarrier.{u} where
  toTorus := (sectionFilling q).filledPresentation
  kind := ![3, 1]
  kind_mem i := by fin_cases i <;> simp
  piece i := Fin.cases (sectionFilling q).filledProductPiece
    (fun i' => Fin.cases (sectionFilling q).filledSolidPiece (fun i'' => i''.elim0) i') i

theorem mergeModel_mergeSlope (q : ℤ) :
    (mergeModel.{u} q).mergeSlope (0 : Fin 1) true = sectionSlope q := by
  change torusUnit (sectionFilling q).matching • meridianSlope = sectionSlope q
  rw [meridianSlope, PrimitiveSlope.smul_mk, sectionSlope, PrimitiveSlope.mk_eq_mk_iff]
  right
  simp [smulVec, val_torusUnit, ConeFilling.torusMatrix_matching, ConeFilling.matchingMatrix,
    ConeFilling.reflectMatrix, ConeFilling.chartMatrix, sectionFilling, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem mergeModel_isMergeSeam (q : ℤ) : (mergeModel.{u} q).IsMergeSeam (0 : Fin 1) true :=
  ⟨rfl, (by norm_num : 2 ≤ 3),
    ((mergeModel.{u} q).fillingDistance_eq_delta_mergeSlope (0 : Fin 1) true).trans
      ((congrArg (fun a => PrimitiveSlope.delta a fiberSlope) (mergeModel_mergeSlope q)).trans
        (delta_sectionSlope_fiberSlope q))⟩

end Merge

namespace Merge

def twistCollar (σ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1) :=
  σ.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)

def twistSigned (σ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) :=
  σ.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)

def twistPD {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (σ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
  (twistCollar σ).toPartialDiffeomorph.trans c

theorem twistPD_apply {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (σ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (p : Torus × EuclideanHalfSpace 1) :
    twistPD c σ p = c (σ p.1, p.2) := rfl

theorem twistPD_source {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (σ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (hc : c.source = halfCollarSource) :
    (twistPD c σ).source = halfCollarSource := by
  change Set.univ ∩ (twistCollar σ) ⁻¹' c.source = _
  rw [hc, Set.univ_inter]
  rfl

theorem orientation_map_trans_symm {A B D : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] [AddCommGroup D] [Module ℝ D] {m : ℕ} (e : A ≃ₗ[ℝ] B)
    (f : B ≃ₗ[ℝ] D) (o : Orientation ℝ D (Fin m)) :
    Orientation.map (Fin m) (e.trans f).symm o =
      Orientation.map (Fin m) e.symm (Orientation.map (Fin m) f.symm o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

theorem reverses_twist {C : CompactCarrier.{u}} {l r : Torus × EuclideanHalfSpace 1 → C.Carrier}
    (σ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hl : ∀ t, MDifferentiableAt halfCollarModel C.model l (t, halfZero))
    (hr : ∀ t, MDifferentiableAt halfCollarModel C.model r (t, halfZero))
    (h : ReversesBoundaryOrientation C l r) :
    ReversesBoundaryOrientation C (fun p => l (σ p.1, p.2)) (fun p => r (σ p.1, p.2)) := by
  intro t
  obtain ⟨L, R, hL, hR, ho⟩ := h (σ t)
  let D := ((twistCollar σ).mfderivToContinuousLinearEquiv (by simp) (t, halfZero)).toLinearEquiv
  have hG : MDifferentiableAt halfCollarModel halfCollarModel (twistCollar σ) (t, halfZero) :=
    (twistCollar σ).contMDiff.mdifferentiableAt (by simp)
  refine ⟨D.trans L, D.trans R, fun v => ?_, fun v => ?_, ?_⟩
  · change L (D v) = mfderiv halfCollarModel C.model (l ∘ twistCollar σ) (t, halfZero) v
    rw [mfderiv_comp (t, halfZero) (hl (σ t)) hG]
    exact hL (D v)
  · change R (D v) = mfderiv halfCollarModel C.model (r ∘ twistCollar σ) (t, halfZero) v
    rw [mfderiv_comp (t, halfZero) (hr (σ t)) hG]
    exact hR (D v)
  · refine (orientation_map_trans_symm D L _).trans ?_
    refine Eq.trans ?_ (congrArg Neg.neg (orientation_map_trans_symm D R _).symm)
    refine (congrArg (Orientation.map (Fin 3) D.symm) ho).trans ?_
    exact Orientation.map_neg _ _

theorem mdifferentiableAt_comp_collar {C : CompactCarrier.{u}}
    (φ : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hφ : φ.source = halfCollarSource) (g : Torus → Torus)
    (hg : ContMDiff torusModel torusModel ∞ g) (t : Torus) :
    MDifferentiableAt halfCollarModel C.model (fun p => φ (g p.1, p.2)) (t, halfZero) := by
  have hφd : MDifferentiableAt halfCollarModel C.model φ (g t, halfZero) :=
    (φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds
      (hφ ▸ zero_mem_halfCollarSource (g t)))).mdifferentiableAt (by simp)
  have hgd : MDifferentiableAt halfCollarModel halfCollarModel
      (fun p : Torus × EuclideanHalfSpace 1 => (g p.1, p.2)) (t, halfZero) :=
    ((hg.comp contMDiff_fst).prodMk contMDiff_snd).mdifferentiableAt (by simp)
  exact hφd.comp (t, halfZero) hgd

end Merge

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (σL σR : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))

def retwistPairing : TorusPairing T.cutCarrier where
  count := T.pairing.count
  gluing := T.pairing.gluing
  leftParam k := (σL k).toHomeomorph.trans (T.pairing.leftParam k)
  rightParam k := (σR k).toHomeomorph.trans (T.pairing.rightParam k)
  matching k := ((σL k).trans (T.pairing.matching k)).trans (σR k).symm
  matching_eq k t := by
    have h := T.pairing.matching_eq k (σL k t)
    change T.pairing.gluing.attaching k (T.pairing.leftParam k (σL k t)) =
      T.pairing.rightParam k (σR k ((σR k).symm (T.pairing.matching k (σL k t))))
    rw [Diffeomorph.apply_symm_apply]
    exact h
  leftCollar k := Merge.twistPD (T.pairing.leftCollar k) (σL k)
  rightCollar k := Merge.twistPD (T.pairing.rightCollar k) (σR k)
  left_source k := Merge.twistPD_source _ _ (T.pairing.left_source k)
  right_source k := Merge.twistPD_source _ _ (T.pairing.right_source k)
  left_zero k t := T.pairing.left_zero k (σL k t)
  right_zero k t := T.pairing.right_zero k (σR k t)
  reversing k := by
    have h := Merge.reverses_twist (σL k)
      (fun t => Merge.mdifferentiableAt_comp_collar (T.pairing.leftCollar k)
        (T.pairing.left_source k) id contMDiff_id t)
      (fun t => Merge.mdifferentiableAt_comp_collar (T.pairing.rightCollar k)
        (T.pairing.right_source k) (T.pairing.matching k) (T.pairing.matching k).contMDiff t)
      (T.pairing.reversing k)
    have he : (fun p : Torus × EuclideanHalfSpace 1 =>
        Merge.twistPD (T.pairing.rightCollar k) (σR k)
          ((((σL k).trans (T.pairing.matching k)).trans (σR k).symm) p.1, p.2)) =
        fun p => T.pairing.rightCollar k (T.pairing.matching k (σL k p.1), p.2) := by
      funext p
      change T.pairing.rightCollar k (σR k ((σR k).symm (T.pairing.matching k (σL k p.1))), p.2) =
        _
      rw [Diffeomorph.apply_symm_apply]
    change ReversesBoundaryOrientation T.cutCarrier
      (fun p => T.pairing.leftCollar k (σL k p.1, p.2)) _
    rw [he]
    exact h

def retwist : TorusPresentation W where
  cutCarrier := T.cutCarrier
  components := T.components
  pairing := T.retwistPairing σL σR
  externalCount := T.externalCount
  external := T.external
  cutExternal := T.cutExternal
  external_exhausted := T.external_exhausted
  cut_boundary_exhausted := T.cut_boundary_exhausted
  external_disjoint := T.external_disjoint
  reconstruction := T.reconstruction
  quotient_smooth := T.quotient_smooth
  quotient_oriented := T.quotient_oriented
  interiorImage := T.interiorImage
  interiorDiffeomorph := T.interiorDiffeomorph
  interior_map := T.interior_map
  seam k := (Merge.twistSigned (σL k)).toPartialDiffeomorph.trans (T.seam k)
  seam_source k := by
    ext p
    change p ∈ Set.univ ∩ (Merge.twistSigned (σL k)) ⁻¹' (T.seam k).source ↔
      p ∈ signedCollarSource
    rw [T.seam_source k]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  seam_zero k t := T.seam_zero k (σL k t)
  seam_positive k t s hs hs1 := by
    have h := T.seam_positive k (σL k t) s hs hs1
    change T.seam k (σL k t, s) = T.reconstruction (T.pairing.quotientMap
      (T.pairing.rightCollar k (σR k ((σR k).symm (T.pairing.matching k (σL k t))),
        halfPoint s hs)))
    rw [Diffeomorph.apply_symm_apply]
    exact h
  seam_negative k t s hs hs1 := T.seam_negative k (σL k t) s hs hs1
  seam_interior k := fun _ hy => T.seam_interior k hy.1
  seam_disjoint i j hij := (T.seam_disjoint hij).mono (fun _ hy => hy.1) (fun _ hy => hy.1)
  marked_collar := T.marked_collar
  external_seam_disjoint i k := (T.external_seam_disjoint i k).mono_right (fun _ hy => hy.1)
  leftPiece := T.leftPiece
  rightPiece := T.rightPiece
  left_owned := T.left_owned
  right_owned := T.right_owned
  externalPiece := T.externalPiece
  external_owned := T.external_owned

def sideTwist : T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  | .inl k => σL k
  | .inr (.inl k) => σR k
  | .inr (.inr _) => Diffeomorph.refl torusModel Torus ∞

theorem retwist_sidePiece : (T.retwist σL σR).sidePiece = T.sidePiece := by
  funext s
  rcases s with k | k | k <;> rfl

theorem retwist_sideCollar_apply (s : T.Side) (p : Torus × EuclideanHalfSpace 1) :
    (T.retwist σL σR).sideCollar s p = T.sideCollar s (T.sideTwist σL σR s p.1, p.2) := by
  rcases s with k | k | k <;> rfl

def ownedSideRetwist (i : Fin T.components.count) :
    T.OwnedSide i ≃ (T.retwist σL σR).OwnedSide i :=
  Equiv.subtypeEquivRight fun s => by rw [retwist_sidePiece]; exact Iff.rfl

theorem pieceCollar_retwist (i : Fin T.components.count) (s : T.OwnedSide i)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.retwist σL σR).pieceCollar i (T.ownedSideRetwist σL σR i s) p).val =
      T.sideCollar s.val (T.sideTwist σL σR s.val p.1, p.2) := by
  exact (TorusPresentation.pieceCollar_apply (T.retwist σL σR) i
    (T.ownedSideRetwist σL σR i s) hp).trans (T.retwist_sideCollar_apply σL σR s.val p)

theorem retwist_pairing_count : (T.retwist σL σR).pairing.count = T.pairing.count := rfl

end TorusPresentation

structure TwistedProductPiece {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W)
    (i : Fin T.components.count) (k : ℕ) where
  base : PlanarBase.{u} k
  port : Fin k ≃ T.OwnedSide i
  trivialization : (base.surface.Carrier × Circle) ≃ₘ⟮
    (SurfaceModel.model base.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯ T.components.piece i
  twist : Fin k → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  collar_eq : ∀ j p, p ∈ halfCollarSource →
    T.pieceCollar i (port j) (twist j p.1, p.2) =
      trivialization (base.collar j (p.1.1, p.2), p.1.2)

namespace TwistedProductPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {i : Fin T.components.count} {k : ℕ}

def ofProduct (P : ProductFibredPiece T i k) : TwistedProductPiece T i k where
  base := P.base
  port := P.port
  trivialization := P.trivialization
  twist _ := Diffeomorph.refl torusModel Torus ∞
  collar_eq j p hp := P.collar_eq j p hp

def toRetwist (P : TwistedProductPiece T i k)
    (σL σR : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (hσ : ∀ j t, T.sideTwist σL σR (P.port j).val t = P.twist j t) :
    ProductFibredPiece (T.retwist σL σR) i k where
  base := P.base
  port := P.port.trans (T.ownedSideRetwist σL σR i)
  trivialization := P.trivialization
  collar_eq j p hp := by
    apply Subtype.ext
    rw [Equiv.trans_apply, T.pieceCollar_retwist σL σR i _ hp, hσ]
    have hq : (P.twist j p.1, p.2) ∈ halfCollarSource := hp
    have h := congrArg Subtype.val (P.collar_eq j p hp)
    rw [T.pieceCollar_apply i _ hq] at h
    exact h

end TwistedProductPiece

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (hext : ∀ i, T.externalPiece i ∉ S)
  (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))

def contractIndex {i : Fin T.components.count} (hi : i ∉ S) :
    Fin (T.contract S hext hk hconn).components.count :=
  (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)).castSucc

theorem subIndexOf_eq_iff {S' : Finset (Fin T.components.count)} {i i' : Fin T.components.count}
    (hi : i ∈ S') (hi' : i' ∈ S') : T.subIndexOf S' hi = T.subIndexOf S' hi' ↔ i = i' := by
  constructor
  · intro h
    have := congrArg (T.subIndex S') h
    rwa [subIndex_subIndexOf, subIndex_subIndexOf] at this
  · rintro rfl
    rfl

theorem contract_sidePiece_eq_contractIndex_iff {i : Fin T.components.count} (hi : i ∉ S)
    (s : (T.contract S hext hk hconn).Side) :
    (T.contract S hext hk hconn).sidePiece s = T.contractIndex S hext hk hconn hi ↔
      T.sidePiece (T.contractLiftSide S hext hk hconn s) = i := by
  rcases s with k | k | e
  · change T.contractLeftPiece S k = _ ↔ T.leftPiece (T.nonInternal S k).val = i
    unfold contractLeftPiece contractIndex
    split_ifs with hl
    · exact iff_of_false (Fin.castSucc_lt_last _).ne' fun he => hi (he ▸ hl)
    · rw [Fin.castSucc_inj]
      exact T.subIndexOf_eq_iff _ _
  · change T.contractRightPiece S k = _ ↔ T.rightPiece (T.nonInternal S k).val = i
    unfold contractRightPiece contractIndex
    split_ifs with hr
    · exact iff_of_false (Fin.castSucc_lt_last _).ne' fun he => hi (he ▸ hr)
    · rw [Fin.castSucc_inj]
      exact T.subIndexOf_eq_iff _ _
  · change T.contractExternalPiece S hext e = _ ↔ T.externalPiece e = i
    unfold contractExternalPiece contractIndex
    rw [Fin.castSucc_inj]
    exact T.subIndexOf_eq_iff _ _

def contractOwnedSideMap {i : Fin T.components.count} (hi : i ∉ S)
    (s : (T.contract S hext hk hconn).OwnedSide (T.contractIndex S hext hk hconn hi)) :
    T.OwnedSide i :=
  ⟨T.contractLiftSide S hext hk hconn s.val,
    (T.contract_sidePiece_eq_contractIndex_iff S hext hk hconn hi s.val).mp s.property⟩

theorem contractOwnedSideMap_bijective {i : Fin T.components.count} (hi : i ∉ S) :
    Function.Bijective (T.contractOwnedSideMap S hext hk hconn hi) := by
  refine ⟨fun a b h => Subtype.ext (T.contractLiftSide_injective S hext hk hconn
    (congrArg Subtype.val h)), fun s => ?_⟩
  have hs : ∀ k c, T.leftPiece k ∈ S → T.rightPiece k ∈ S → s.val ≠ T.pairSide k c := by
    intro k c hl hr he
    apply hi
    rw [← s.property, he]
    cases c
    · exact hr
    · exact hl
  obtain ⟨s', hs'⟩ := T.exists_contractLiftSide_eq S hext hk hconn s.val hs
  refine ⟨⟨s', (T.contract_sidePiece_eq_contractIndex_iff S hext hk hconn hi s').mpr
    (by rw [hs']; exact s.property)⟩, Subtype.ext hs'⟩

def contractOwnedSideEquiv {i : Fin T.components.count} (hi : i ∉ S) :
    (T.contract S hext hk hconn).OwnedSide (T.contractIndex S hext hk hconn hi) ≃
      T.OwnedSide i :=
  Equiv.ofBijective _ (T.contractOwnedSideMap_bijective S hext hk hconn hi)

theorem contractLiftSide_contractOwnedSideEquiv_symm {i : Fin T.components.count} (hi : i ∉ S)
    (s : T.OwnedSide i) :
    T.contractLiftSide S hext hk hconn ((T.contractOwnedSideEquiv S hext hk hconn hi).symm s).val =
      s.val :=
  congrArg Subtype.val ((T.contractOwnedSideEquiv S hext hk hconn hi).apply_symm_apply s)

theorem contract_sideCollar_apply (s : (T.contract S hext hk hconn).Side)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (T.contract S hext hk hconn).sideCollar s p =
      T.contractMap S hext hk (T.sideCollar (T.contractLiftSide S hext hk hconn s) p) := by
  rcases s with k | k | e
  · exact T.contractLeftCollar_apply S hext hk k hp
  · exact T.contractRightCollar_apply S hext hk k hp
  · exact T.contractExternalCollar_apply S hext hk e hp

def contractPieceDiffeomorph {i : Fin T.components.count} (hi : i ∉ S) :
    T.components.piece i ≃ₘ⟮T.cutCarrier.model, (T.contract S hext hk hconn).cutCarrier.model⟯
      (T.contract S hext hk hconn).components.piece (T.contractIndex S hext hk hconn hi) where
  toFun x := ⟨Sum.inl ⟨x.val, T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hi) x.property⟩,
    by
      change _ ∈ (T.contractPiece S hext hk (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)).castSucc :
        Set (T.ContractCut S hext hk))
      rw [T.contractPiece_castSucc S hext hk]
      refine ⟨_, ?_, rfl⟩
      change x.val ∈ T.components.piece (T.subIndex Sᶜ _)
      rw [subIndex_subIndexOf]
      exact x.property⟩
  invFun y := ⟨Sum.elim (fun a => a.val)
      (fun _ => (T.components.connected i).toNonempty.some.val) y.val, by
    have hy : y.val ∈ Sum.inl '' (T.subPieceOf Sᶜ (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)) :
        Set (T.subCarrier Sᶜ).Carrier) := by
      rw [← T.contractPiece_castSucc S hext hk]
      exact y.property
    obtain ⟨a, ha, he⟩ := hy
    rw [← he]
    change a.val ∈ T.components.piece i
    have ha' : a.val ∈ T.components.piece (T.subIndex Sᶜ _) := ha
    rwa [subIndex_subIndexOf] at ha'⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Sum.inl '' (T.subPieceOf Sᶜ (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)) :
        Set (T.subCarrier Sᶜ).Carrier) := by
      rw [← T.contractPiece_castSucc S hext hk]
      exact hy
    obtain ⟨a, -, rfl⟩ := hy'
    rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    have h1 : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (fun x : T.components.piece i => (⟨x.val, T.piece_subset_subPiece Sᶜ
          (Finset.mem_compl.mpr hi) x.property⟩ : (T.subCarrier Sᶜ).Carrier)) :=
      (ContMDiff.subtypeVal_comp_iff (I := T.cutCarrier.model) (I' := T.cutCarrier.model)
        (T.subPiece Sᶜ) _).mp contMDiff_subtype_val
    have h2 : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (fun x : T.components.piece i => (Sum.inl ⟨x.val, T.piece_subset_subPiece Sᶜ
          (Finset.mem_compl.mpr hi) x.property⟩ : T.ContractCut S hext hk)) :=
      (ContMDiff.inl (I := T.cutCarrier.model) (M := (T.subCarrier Sᶜ).Carrier)
        (M' := (T.contractRegion S hext hk).Carrier)).comp h1
    exact h2
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    have h1 : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (Sum.elim (fun a : (T.subCarrier Sᶜ).Carrier => a.val)
          (fun _ : (T.contractRegion S hext hk).Carrier =>
            (T.components.connected i).toNonempty.some.val)) :=
      ContMDiff.sumElim (contMDiff_subtype_val (I := T.cutCarrier.model) (U := T.subPiece Sᶜ))
        contMDiff_const
    exact h1.comp (contMDiff_subtype_val (I := (T.contract S hext hk hconn).cutCarrier.model)
      (U := (T.contract S hext hk hconn).components.piece (T.contractIndex S hext hk hconn hi)))

theorem contractPieceDiffeomorph_apply {i : Fin T.components.count} (hi : i ∉ S)
    (x : T.components.piece i) :
    (T.contractPieceDiffeomorph S hext hk hconn hi x).val =
      Sum.inl ⟨x.val, T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hi) x.property⟩ := rfl

end TorusPresentation

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {S : Finset (Fin T.components.count)} {hext : ∀ i, T.externalPiece i ∉ S}
  {hk : T.cutCarrier.kind = .withBoundary}
  {hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S)}
  {i : Fin T.components.count} {k : ℕ}

def contractTransport (P : ProductFibredPiece T i k) (hi : i ∉ S) :
    ProductFibredPiece (T.contract S hext hk hconn) (T.contractIndex S hext hk hconn hi) k where
  base := P.base
  port := P.port.trans (T.contractOwnedSideEquiv S hext hk hconn hi).symm
  trivialization := P.trivialization.trans (T.contractPieceDiffeomorph S hext hk hconn hi)
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp,
      T.contract_sideCollar_apply S hext hk hconn _ hp,
      Equiv.trans_apply, T.contractLiftSide_contractOwnedSideEquiv_symm S hext hk hconn hi]
    have hmem : T.sideCollar (P.port j).val p ∈ T.subPiece Sᶜ :=
      T.piece_subset_subPiece Sᶜ (Finset.mem_compl.mpr hi)
        (T.sideCollar_target_subset_of_owned i (P.port j)
          ((T.sideCollar (P.port j).val).map_source' ((T.sideCollar_source _).symm ▸ hp)))
    rw [T.contractMap_of_mem S hext hk hmem]
    change _ = (T.contractPieceDiffeomorph S hext hk hconn hi
      (P.trivialization (P.base.collar j (p.1.1, p.2), p.1.2))).val
    rw [T.contractPieceDiffeomorph_apply S hext hk hconn hi]
    congr 2
    rw [← P.collar_eq j p hp, T.pieceCollar_apply i _ hp]

end ProductFibredPiece

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}

def castIndex {i i' : Fin T.components.count} {k k' : ℕ} (P : ProductFibredPiece T i k)
    (hi : i = i') (hk : k = k') : ProductFibredPiece T i' k' :=
  hi ▸ hk ▸ P

end ProductFibredPiece

namespace TwistedProductPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {i : Fin T.components.count} {k : ℕ}

def leftTwist (P : TwistedProductPiece T i k) (l : Fin T.pairing.count) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  if hl : T.leftPiece l = i then P.twist (P.port.symm ⟨.inl l, hl⟩)
  else Diffeomorph.refl torusModel Torus ∞

def rightTwist (P : TwistedProductPiece T i k) (l : Fin T.pairing.count) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  if hr : T.rightPiece l = i then P.twist (P.port.symm ⟨.inr (.inl l), hr⟩)
  else Diffeomorph.refl torusModel Torus ∞

theorem sideTwist_eq (P : TwistedProductPiece T i k) (hx : ∀ e, T.externalPiece e ≠ i)
    (s : T.OwnedSide i) :
    T.sideTwist P.leftTwist P.rightTwist s.val = P.twist (P.port.symm s) := by
  obtain ⟨s, hs⟩ := s
  rcases s with l | l | e
  · exact dite_eq_left hs
  · exact dite_eq_left hs
  · exact absurd hs (hx e)

theorem sideTwist_eq_refl (P : TwistedProductPiece T i k) {i' : Fin T.components.count}
    (hne : i' ≠ i) (s : T.OwnedSide i') :
    T.sideTwist P.leftTwist P.rightTwist s.val = Diffeomorph.refl torusModel Torus ∞ := by
  obtain ⟨s, hs⟩ := s
  rcases s with l | l | e
  · exact dite_eq_right fun hl => hne (hs.symm.trans hl)
  · exact dite_eq_right fun hr => hne (hs.symm.trans hr)
  · rfl

def toProduct (P : TwistedProductPiece T i k) (hx : ∀ e, T.externalPiece e ≠ i) :
    ProductFibredPiece (T.retwist P.leftTwist P.rightTwist) i k :=
  P.toRetwist _ _ fun j t => by rw [P.sideTwist_eq hx, Equiv.symm_apply_apply]

end TwistedProductPiece

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}

def retwistOther {i i' : Fin T.components.count} {k k' : ℕ} (R : ProductFibredPiece T i' k')
    (P : TwistedProductPiece T i k) (hne : i' ≠ i) :
    ProductFibredPiece (T.retwist P.leftTwist P.rightTwist) i' k' :=
  (TwistedProductPiece.ofProduct R).toRetwist _ _ fun j t => by
    rw [P.sideTwist_eq_refl hne]
    rfl

end ProductFibredPiece

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
  (hf : E.HostSelfSeamFree j b) (hext : ∀ i, E.toTorus.externalPiece i ∉ E.toTorus.seamPair j)

theorem mergeContraction_externalPiece_ne
    (e : Fin (E.mergeContraction j b h hf hext).externalCount) :
    (E.mergeContraction j b h hf hext).externalPiece e ≠ E.mergeLast j b h hf hext :=
  (Fin.castSucc_lt_last _).ne

theorem mergeContraction_card_ownedSide_last :
    Fintype.card ((E.mergeContraction j b h hf hext).OwnedSide (E.mergeLast j b h hf hext)) =
      E.kind (E.hostPiece j b) - 1 := by
  let S := E.toTorus.seamPair j
  have hk := E.toTorus.cutCarrier_kind_of_pos j.pos
  have hconn := h.isConnected_region hf hext
  have hj : E.toTorus.leftPiece j ∈ S ∧ E.toTorus.rightPiece j ∈ S :=
    ⟨E.toTorus.left_mem_seamPair j, E.toTorus.right_mem_seamPair j⟩
  let a : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨_, E.sidePiece_pairSide j !b⟩
  have hH : ∀ s : (E.toTorus.contract S hext hk hconn).OwnedSide
      (E.toTorus.contractLast S hext hk hconn),
      E.toTorus.sidePiece (E.toTorus.contractLiftSide S hext hk hconn s.val) =
        E.hostPiece j b := by
    intro s
    have hmem := (E.toTorus.contract_sidePiece_eq_last_iff S hext hk hconn s.val).mp s.property
    rcases (E.mem_seamPair_iff j b _).mp hmem with hV | hA
    · exact absurd (h.eq_pairSide hV)
        (E.toTorus.contractLiftSide_ne_pairSide S hext hk hconn hj s.val b)
    · exact hA
  let f : (E.toTorus.contract S hext hk hconn).OwnedSide (E.toTorus.contractLast S hext hk hconn) →
      {s : E.toTorus.OwnedSide (E.hostPiece j b) // s ≠ a} := fun s =>
    ⟨⟨E.toTorus.contractLiftSide S hext hk hconn s.val, hH s⟩, fun he =>
      E.toTorus.contractLiftSide_ne_pairSide S hext hk hconn hj s.val (!b)
        (congrArg Subtype.val he)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (E.toTorus.contractLiftSide_injective S hext hk hconn
      (congrArg (fun z => z.val.val) hxy)), fun s => ?_⟩
    have hs : ∀ k c, E.toTorus.leftPiece k ∈ S → E.toTorus.rightPiece k ∈ S →
        s.val.val ≠ E.toTorus.pairSide k c := by
      intro k c hl hr he
      obtain rfl := h.eq_of_internal hf hl hr
      by_cases hc : c = b
      · subst hc
        apply h.seamPiece_ne_hostPiece
        rw [← E.sidePiece_pairSide k c, ← he]
        exact s.val.property
      · have hc' : c = !b := by cases c <;> cases b <;> simp_all
        subst hc'
        exact s.property (Subtype.ext he)
    obtain ⟨s', hs'⟩ := E.toTorus.exists_contractLiftSide_eq S hext hk hconn s.val.val hs
    refine ⟨⟨s', ?_⟩, Subtype.ext (Subtype.ext hs')⟩
    rw [TorusPresentation.contract_sidePiece_eq_last_iff, hs', s.val.property]
    exact (E.mem_seamPair_iff j b _).mpr (Or.inr rfl)
  change Fintype.card ((E.toTorus.contract S hext hk hconn).OwnedSide
    (E.toTorus.contractLast S hext hk hconn)) = _
  rw [Fintype.card_congr (Equiv.ofBijective f hbij), Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, E.card_ownedSide_eq_kind]

theorem exists_of_twistedProductPiece
    (P : TwistedProductPiece (E.mergeContraction j b h hf hext) (E.mergeLast j b h hf hext)
      (E.kind (E.hostPiece j b) - 1)) :
    ∃ E' : ElementaryPresentation W, E'.complexity + 1 = E.complexity := by
  let S := E.toTorus.seamPair j
  let hk := E.toTorus.cutCarrier_kind_of_pos j.pos
  let hconn := h.isConnected_region hf hext
  let kind' : Fin (Sᶜ.card + 1) → ℕ := Fin.lastCases (E.kind (E.hostPiece j b) - 1)
    fun m => E.kind (E.toTorus.subIndex Sᶜ m)
  have hkl : E.kind (E.hostPiece j b) - 1 = kind' (Fin.last _) := by
    simp only [kind', Fin.lastCases_last]
  have hkc : ∀ m, E.kind (E.toTorus.subIndex Sᶜ m) = kind' m.castSucc := by
    intro m
    simp only [kind', Fin.lastCases_castSucc]
  have hmem : ∀ m, E.toTorus.subIndex Sᶜ m ∉ S := fun m =>
    Finset.mem_compl.mp (E.toTorus.subIndex_mem Sᶜ m)
  let T'' := (E.mergeContraction j b h hf hext).retwist P.leftTwist P.rightTwist
  have hkm : ∀ i', kind' i' ∈ ({1, 2, 3} : Finset ℕ) := by
    intro i'
    induction i' using Fin.lastCases with
    | last =>
      rw [← hkl]
      have h2 := h.two_le_kind_hostPiece
      rcases E.kind_eq_one_or_two_or_three (E.hostPiece j b) with h3 | h3 | h3 <;>
        simp [h3] at h2 ⊢
    | cast m =>
      rw [← hkc]
      exact E.kind_mem _
  refine ⟨⟨T'', kind', hkm, fun i' => ?_⟩, ?_⟩
  · induction i' using Fin.lastCases with
    | last =>
      exact (P.toProduct (E.mergeContraction_externalPiece_ne j b h hf hext)).castIndex rfl hkl
    | cast m =>
      exact (((E.piece (E.toTorus.subIndex Sᶜ m)).contractTransport (S := S) (hext := hext)
        (hk := hk) (hconn := hconn) (hmem m)).retwistOther P
          (Fin.castSucc_lt_last _).ne).castIndex
        (congrArg Fin.castSucc (E.toTorus.subIndexOf_subIndex Sᶜ m)) (hkc m)
  · exact E.mergeContraction_pairing_count j b h hf hext

end ElementaryPresentation

namespace ElementaryPresentation

namespace IsMergeSeam

variable {W : CompactCarrier.{u}} {E : ElementaryPresentation W}
  {j : Fin E.toTorus.pairing.count} {b : Bool}

theorem exists_selfSeam (hs : ¬ E.HostSelfSeamFree j b) :
    ∃ k, E.toTorus.leftPiece k = E.hostPiece j b ∧ E.toTorus.rightPiece k = E.hostPiece j b := by
  simp only [HostSelfSeamFree, not_forall, not_not] at hs
  obtain ⟨k, hl, hr⟩ := hs
  exact ⟨k, hl, hr⟩

theorem ne_of_selfSeam (h : E.IsMergeSeam j b) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k = E.hostPiece j b) (hr : E.toTorus.rightPiece k = E.hostPiece j b) :
    k ≠ j := by
  rintro rfl
  apply h.seamPiece_ne_hostPiece
  cases b
  · exact hr
  · exact hl

theorem host_sides (h : E.IsMergeSeam j b) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k = E.hostPiece j b) (hr : E.toTorus.rightPiece k = E.hostPiece j b) :
    E.kind (E.hostPiece j b) = 3 ∧ ∀ s : E.toTorus.Side, E.toTorus.sidePiece s = E.hostPiece j b →
      s = E.toTorus.pairSide j !b ∨ s = .inl k ∨ s = .inr (.inl k) := by
  have hkj := h.ne_of_selfSeam hl hr
  let a : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨_, E.sidePiece_pairSide j !b⟩
  let a1 : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨.inl k, hl⟩
  let a2 : E.toTorus.OwnedSide (E.hostPiece j b) := ⟨.inr (.inl k), hr⟩
  have h3 : ({a, a1, a2} : Finset (E.toTorus.OwnedSide (E.hostPiece j b))).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨a, a1, a2, fun he => ?_, fun he => ?_, fun he => ?_, rfl⟩
    · exact E.toTorus.pairSide_ne_of_ne hkj.symm (!b) true (congrArg Subtype.val he)
    · exact E.toTorus.pairSide_ne_of_ne hkj.symm (!b) false (congrArg Subtype.val he)
    · exact E.toTorus.pairSide_ne_not k true (congrArg Subtype.val he)
  have hle := Finset.card_le_univ ({a, a1, a2} : Finset (E.toTorus.OwnedSide (E.hostPiece j b)))
  rw [h3, E.card_ownedSide_eq_kind] at hle
  have hk3 : E.kind (E.hostPiece j b) = 3 := by
    rcases E.kind_eq_one_or_two_or_three (E.hostPiece j b) with h' | h' | h' <;> omega
  refine ⟨hk3, fun s hs => ?_⟩
  have hall : ({a, a1, a2} : Finset (E.toTorus.OwnedSide (E.hostPiece j b))) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h3, E.card_ownedSide_eq_kind, hk3]
  have hmem : (⟨s, hs⟩ : E.toTorus.OwnedSide (E.hostPiece j b)) ∈
      ({a, a1, a2} : Finset (E.toTorus.OwnedSide (E.hostPiece j b))) := by
    rw [hall]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with he | he | he
  · exact Or.inl (congrArg Subtype.val he)
  · exact Or.inr (Or.inl (congrArg Subtype.val he))
  · exact Or.inr (Or.inr (congrArg Subtype.val he))

theorem not_isCrossing (h : E.IsMergeSeam j b) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k = E.hostPiece j b) (hr : E.toTorus.rightPiece k = E.hostPiece j b)
    (k' : Fin E.toTorus.pairing.count) : ¬ E.toTorus.IsCrossing (E.toTorus.seamPair j) k' := by
  have hside : ∀ c, E.toTorus.sidePiece (E.toTorus.pairSide k' c) ∈ E.toTorus.seamPair j →
      k' = j ∨ k' = k := by
    intro c hc
    rcases (E.mem_seamPair_iff j b _).mp hc with hV | hA
    · have he := h.eq_pairSide hV
      cases c <;> cases b <;> simp_all [TorusPresentation.pairSide]
    · rcases (h.host_sides hl hr).2 _ hA with he | he | he <;>
        cases c <;> cases b <;> simp_all [TorusPresentation.pairSide]
  have hboth : ∀ c, E.toTorus.sidePiece (E.toTorus.pairSide k' c) ∈ E.toTorus.seamPair j →
      E.toTorus.leftPiece k' ∈ E.toTorus.seamPair j ∧
        E.toTorus.rightPiece k' ∈ E.toTorus.seamPair j := by
    intro c hc
    rcases hside c hc with rfl | rfl
    · exact ⟨E.toTorus.left_mem_seamPair _, E.toTorus.right_mem_seamPair _⟩
    · rw [hl, hr]
      have hA : E.hostPiece j b ∈ E.toTorus.seamPair j :=
        (E.mem_seamPair_iff j b _).mpr (Or.inr rfl)
      exact ⟨hA, hA⟩
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact h2 (hboth true h1).2
  · exact h2 (hboth false h1).1

end IsMergeSeam

namespace IsMergeSeam

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool}

theorem mem_seamPair_of_selfSeam (h : E.IsMergeSeam j b) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k = E.hostPiece j b) (hr : E.toTorus.rightPiece k = E.hostPiece j b)
    (i : Fin E.toTorus.components.count) : i ∈ E.toTorus.seamPair j := by
  let T := E.toTorus
  let S := T.seamPair j
  have hcross : T.crossingSurface S = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨k', hk', -⟩ := Set.mem_iUnion₂.mp hy
    exact h.not_isCrossing hl hr k' hk'
  have hdisj : ∀ y, y ∈ Set.range (T.restrictMap S) → y ∉ T.complImage S := fun y h1 h2 => by
    have := T.range_inter_complImage_subset_crossing S ⟨h1, h2⟩
    rw [hcross] at this
    exact this
  have hcov := T.range_union_complImage S
  have hrange : Set.range (T.restrictMap S) = (T.complImage S)ᶜ := by
    ext y
    constructor
    · exact hdisj y
    · intro hy
      have hu : y ∈ Set.range (T.restrictMap S) ∪ T.complImage S := hcov ▸ Set.mem_univ y
      rcases hu with h1 | h1
      · exact h1
      · exact absurd h1 hy
  obtain ⟨x0⟩ := (T.components.connected (T.leftPiece j)).toNonempty
  have hne : (Set.range (T.restrictMap S)).Nonempty :=
    ⟨_, Set.mem_range_self ((T.restrictPairing S).quotientMap
      ⟨x0.val, T.piece_subset_subPiece S (T.left_mem_seamPair j) x0.property⟩)⟩
  have huniv : Set.range (T.restrictMap S) = Set.univ :=
    IsClopen.eq_univ ⟨T.isClosed_range_restrictMap S,
      hrange ▸ (T.isClosed_complImage S).isOpen_compl⟩ hne
  by_contra hi
  obtain ⟨x⟩ := (T.components.connected i).toNonempty
  have hx : x.val ∉ T.subPiece S := fun hxS => hi (T.mem_of_mem_subPiece S hxS x.property)
  exact hdisj _ (huniv ▸ Set.mem_univ _) ⟨x.val, hx, rfl⟩

theorem components_count_of_selfSeam (h : E.IsMergeSeam j b) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k = E.hostPiece j b) (hr : E.toTorus.rightPiece k = E.hostPiece j b) :
    E.toTorus.components.count = 2 := by
  have huniv : (Finset.univ : Finset (Fin E.toTorus.components.count)) = E.toTorus.seamPair j :=
    (Finset.eq_univ_of_forall (h.mem_seamPair_of_selfSeam hl hr)).symm
  rw [← Fintype.card_fin E.toTorus.components.count, ← Finset.card_univ, huniv,
    TorusPresentation.seamPair, Finset.card_pair h.leftPiece_ne_rightPiece]

theorem complexity_of_selfSeam (h : E.IsMergeSeam j b) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k = E.hostPiece j b) (hr : E.toTorus.rightPiece k = E.hostPiece j b) :
    E.complexity = 2 := by
  have huniv : (Finset.univ : Finset (Fin E.toTorus.components.count)) =
      {E.seamPiece j b, E.hostPiece j b} := by
    refine (Finset.eq_univ_of_forall fun i => ?_).symm
    rcases (E.mem_seamPair_iff j b i).mp (h.mem_seamPair_of_selfSeam hl hr i) with he | he <;>
      simp [he]
  have hside : Fintype.card E.toTorus.Side = 4 := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv E.toTorus.sidePiece), Fintype.card_sigma]
    change ∑ i, Fintype.card (E.toTorus.OwnedSide i) = 4
    simp only [E.card_ownedSide_eq_kind]
    rw [huniv, Finset.sum_pair h.seamPiece_ne_hostPiece, h.1, (h.host_sides hl hr).1]
  have hext := E.toTorus.externalCount_eq_zero
  have hcard : Fintype.card E.toTorus.Side =
      E.toTorus.pairing.count + (E.toTorus.pairing.count + E.toTorus.externalCount) := by
    simp only [TorusPresentation.Side, Fintype.card_sum, Fintype.card_fin]
  unfold complexity
  omega

end IsMergeSeam

end ElementaryPresentation

namespace ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

end ElementaryPresentation

end GC.Seifert
