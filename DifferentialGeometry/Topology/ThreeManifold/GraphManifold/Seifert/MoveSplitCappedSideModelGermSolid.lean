import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelCover

/-!
# The capped solid tori on the filling disc

Lane N2f, side model, step 7 (germ data). The solid torus of side `t` is `germSolid S t (x, u) =
solMap (x, u)` on the filling disc `discPlanarBase 1` of radius `3`. The torus holonomy `sideHol`
is `(a, b) ↦ (b⁻¹, b^(e₀ d) a^(e₁))`. On the collar of the disc of depth `s < 1/3` the solid torus
reads the host collar of the port `sidePort` at depth `s` through `sideHol`
(`germSolid_collar`), and for `s` below the collar width of the split data it is the side collar of
the port in the cut carrier (`liftMap_eq_sideCollar`). The solid torus is injective, it covers the
cap and the core points of the split region on its side, its values are cap points or core points of
the split region, and the two solid tori meet only on their boundary tori.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

open SplitTube

def germHol (k e : ℤ) (he : e = 1 ∨ e = -1) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus where
  toFun p := (p.2⁻¹, p.2 ^ k * p.1 ^ e)
  invFun p := ((p.2 * (p.1⁻¹ ^ k)⁻¹) ^ e, p.1⁻¹)
  left_inv p := by
    simp only [inv_inv, mul_inv_cancel_comm, zpow_zpow_unit he]
  right_inv p := by
    refine Prod.ext (inv_inv _) ?_
    change p.1⁻¹ ^ k * ((p.2 * (p.1⁻¹ ^ k)⁻¹) ^ e) ^ e = p.2
    rw [zpow_zpow_unit he, mul_comm p.2, mul_inv_cancel_left]
  contMDiff_toFun :=
    (contMDiff_snd.inv).prodMk (((contMDiff_circle_zpow' k).comp contMDiff_snd).mul
      ((contMDiff_circle_zpow' e).comp contMDiff_fst))
  contMDiff_invFun :=
    ((contMDiff_circle_zpow' e).comp (contMDiff_snd.mul
      (((contMDiff_circle_zpow' k).comp contMDiff_fst.inv).inv))).prodMk contMDiff_fst.inv

theorem germHol_apply (k e : ℤ) (he : e = 1 ∨ e = -1) (p : Torus) :
    germHol k e he p = (p.2⁻¹, p.2 ^ k * p.1 ^ e) :=
  rfl

def collarHol (k e : ℤ) (he : e = 1 ∨ e = -1) :
    ((Circle × EuclideanHalfSpace 1) × Circle) ≃ₘ⟮circleCollarModel.prod (𝓡 1),
      halfCollarModel⟯ (Torus × EuclideanHalfSpace 1) where
  toFun q := (germHol k e he (q.1.1, q.2), q.1.2)
  invFun p := ((((germHol k e he).symm p.1).1, p.2), ((germHol k e he).symm p.1).2)
  left_inv q := by simp
  right_inv p := by simp
  contMDiff_toFun :=
    ((germHol k e he).contMDiff.comp ((contMDiff_fst.comp contMDiff_fst).prodMk
      contMDiff_snd)).prodMk (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun :=
    (((contMDiff_fst.comp ((germHol k e he).symm.contMDiff.comp contMDiff_fst)).prodMk
      contMDiff_snd).prodMk
      (contMDiff_snd.comp ((germHol k e he).symm.contMDiff.comp contMDiff_fst)))

theorem halfPoint_coord (σ : EuclideanHalfSpace 1) : halfPoint (σ.val 0) σ.2 = σ := by
  apply Subtype.ext
  ext i
  fin_cases i
  rfl

theorem collarDepth_three_sub (s : ℝ) : collarDepth (3 - 3 * s / 2) = s := by
  unfold collarDepth
  ring

theorem norm_three_sub_smul {s : ℝ} (hs : s < 2) (θ : Circle) :
    ‖((3 - 3 * s / 2 : ℝ) • (θ : ℂ))‖ = 3 - 3 * s / 2 := by
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]

section Collar

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)

def sideHol : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  germHol ((E.splitCharts h hlin).e₀ * (E.splitCharts h hlin).d) (E.splitCharts h hlin).e₁
    (E.splitCharts h hlin).he₁

theorem hostPt_collar_of_lt (l : Fin 3) (θ ν : Circle) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (hδ : s < (E.splitData h).δ) :
    E.hostPt h (planarCollarFormula 3 l ((θ : ℂ), s)) ν =
      E.toTorus.sideCollar (E.standardPort (E.hostPiece j b) h.2.1 l).val
        ((θ, ν), halfPoint s hs) := by
  have hp : ((θ, ν), halfPoint s hs) ∈ halfCollarSource := hs1
  have e1 := TorusPresentation.pieceCollar_apply E.toTorus (E.hostPiece j b)
    (E.standardPort (E.hostPiece j b) h.2.1 l) hp
  have e2 := (E.splitData h).hH l ((θ, ν), halfPoint s hs) hp hδ
  rw [← e1, e2]
  change ((E.splitData h).ΘH (clampPants (planarCollarFormula 3 l ((θ : ℂ), s)), ν) :
      E.toTorus.cutCarrier.Carrier) =
    ((E.splitData h).ΘH (pantsPlanarBase.{u}.collar l (θ, halfPoint s hs), ν) :
      E.toTorus.cutCarrier.Carrier)
  rw [pantsCollar_eq l hs hs1]

theorem liftMap_eq_sideCollar (t : Bool) (θ u : Circle) {s : ℝ} (hs : 0 ≤ s) (hs3 : s < 1 / 3)
    (hδ : s < (E.splitData h).δ) :
    (E.splitCharts h hlin).liftMap t ((3 - 3 * s / 2 : ℝ) • (θ : ℂ), u) =
      E.toTorus.cutMap (E.toTorus.sideCollar (E.portSide' h t)
        (E.sideHol h hlin (θ, u), halfPoint s hs)) := by
  have hn := norm_three_sub_smul (s := s) (by linarith) θ
  rw [SplitCharts.liftMap_of_gt _ t (by rw [hn]; linarith)]
  unfold SplitCharts.liftH
  rw [hn, sideData_point_collar _ t (by linarith) (by linarith), hostChart_hostInv,
    collarDepth_three_sub, unitOf_smul (by linarith) θ]
  change E.toTorus.cutMap (E.hostPt h _ _) = _
  rw [E.hostPt_collar_of_lt h _ _ _ hs (by linarith) hδ]
  rfl

end Collar

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool} {h : E.IsSplitSeam j b} {hlin : E.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (E.splitSeamTube j b h hlin)}

theorem norm_embedding_le (x : (discPlanarBase.{u} 1).surface.Carrier) :
    ‖(discPlanarBase.{u} 1).embedding x‖ ≤ 3 :=
  (mem_discSet_iff _).mp x.2

theorem embedding_injective : Injective (discPlanarBase.{u} 1).embedding :=
  (discPlanarBase.{u} 1).isSmoothEmbedding.isEmbedding.injective

theorem embedding_clampDisc {z : ℂ} (hz : ‖z‖ ≤ 3) :
    (discPlanarBase.{u} 1).embedding (clampDisc.{u} z) = z :=
  congrArg ULift.down (clampDisc_val hz)

theorem embedding_collar (θ : Circle) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (discPlanarBase.{u} 1).embedding ((discPlanarBase.{u} 1).collar 0 (θ, halfPoint s hs)) =
      (3 - 3 * s / 2 : ℝ) • (θ : ℂ) := by
  rw [discCollar_eq hs hs1]
  exact embedding_clampDisc (by rw [norm_three_sub_smul (by linarith)]; linarith)

theorem onSolidBoundary_of_norm {q : (discPlanarBase.{u} 1).surface.Carrier × Circle}
    (h3 : ‖(discPlanarBase.{u} 1).embedding q.1‖ = 3) : OnSolidBoundary q := by
  refine ⟨(unitOf ((discPlanarBase.{u} 1).embedding q.1), q.2), Prod.ext ?_ rfl⟩
  apply embedding_injective
  have e : (discPlanarBase.{u} 1).embedding ((discPlanarBase.{u} 1).collar 0
      (unitOf ((discPlanarBase.{u} 1).embedding q.1), halfZero)) =
      (3 : ℝ) • ((unitOf ((discPlanarBase.{u} 1).embedding q.1) : Circle) : ℂ) :=
    discCollar_zero_val.{u} 1 _
  rw [e, ← h3, norm_smul_unitOf]

variable (S : ∀ t, E.SideCap h hlin K t)

def germSolid (t : Bool) (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) : N.Carrier :=
  (S t).solMap ((discPlanarBase.{u} 1).embedding q.1, q.2)

theorem germSolid_injective (t : Bool) : Injective (germSolid S t) := by
  intro q q' he
  have e := (S t).solMap_injOn (norm_embedding_le q.1) (norm_embedding_le q'.1) he
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
  exact Prod.ext (embedding_injective e1) e2

theorem germSolid_collar (t : Bool) (p : Torus) (s : ℝ) (hs : 0 ≤ s) (hs3 : s < 1 / 3) :
    germSolid S t ((discPlanarBase.{u} 1).collar 0 (p.1, halfPoint s hs), p.2) =
      coreMap K (E.hostMap h (planarCollarFormula 3 (sidePort (E.hostSide h) t)
        (((E.sideHol h hlin p).1 : ℂ), 1 * s), (E.sideHol h hlin p).2)) := by
  have hn := norm_three_sub_smul (s := s) (by linarith) p.1
  unfold germSolid
  rw [embedding_collar p.1 hs (by linarith), (S t).solMap_collar (by rw [hn]; linarith)
    (by rw [hn]; linarith), hn, collarDepth_three_sub, one_mul]
  unfold liftFib
  rw [unitOf_smul (by linarith) p.1]
  rfl

theorem germSolid_cap_mem (t : Bool) (w : ClosedCell 3) :
    ∃ q, germSolid S t q = K.cap ((), t) w := by
  obtain ⟨q, hq, he⟩ := (S t).exists_solMap_eq_cap w
  refine ⟨(clampDisc.{u} q.1, q.2), ?_⟩
  unfold germSolid
  rw [embedding_clampDisc hq]
  exact he

theorem germSolid_core_mem {y : E.toTorus.cutCarrier.Carrier}
    (hy : E.InSplitRegion (j := j) (b := b) y)
    (hc : E.toTorus.cutMap y ∈ (E.splitSeamTube j b h hlin).core) :
    ∃ t q, germSolid S t q = coreMap K (E.toTorus.cutMap y) := by
  obtain ⟨t, q, hq, he⟩ := exists_solMap_eq_of_splitRegion S hy hc
  refine ⟨t, (clampDisc.{u} q.1, q.2), ?_⟩
  unfold germSolid
  rw [embedding_clampDisc hq]
  exact he

theorem germSolid_image (t : Bool) (q : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    (∃ w, germSolid S t q = K.cap ((), t) w) ∨ ∃ y : E.toTorus.cutCarrier.Carrier,
      E.InSplitRegion (j := j) (b := b) y ∧
        E.toTorus.cutMap y ∈ (E.splitSeamTube j b h hlin).core ∧
          germSolid S t q = coreMap K (E.toTorus.cutMap y) :=
  (S t).solMap_image (norm_embedding_le q.1)

theorem germSolid_boundary_of_eq (q q' : (discPlanarBase.{u} 1).surface.Carrier × Circle)
    (he : germSolid S false q = germSolid S true q') :
    OnSolidBoundary q ∧ OnSolidBoundary q' := by
  obtain ⟨h1, h2⟩ := solMap_cross (S false) (S true) (norm_embedding_le q.1)
    (norm_embedding_le q'.1) he
  exact ⟨onSolidBoundary_of_norm h1, onSolidBoundary_of_norm h2⟩

end GC.Seifert.ElementaryPresentation
