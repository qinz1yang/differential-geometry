import DifferentialGeometry.Geometry.Collapse.ZeroModel.KleinParam
import DifferentialGeometry.Geometry.Collapse.ZeroModel.SpaceFormDescend
import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.Descend
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.Quotient

/-!
# The Klein parametrisation of the lens space `L(4, -1)`

Lane LFR54-QUOT (Q2). With the explicit map `kleinW` of `KleinParam`:
* `kleinTheta : T² × ℝ → L(4, -1)` is smooth (`contMDiff_kleinTheta`, through the covering
  `ℝ² × ℝ → T² × ℝ`) and invariant under the Klein deck map `(x, y, t) ↦ (x + ½, -y, -t)`
  (`kleinTheta_deck`); its model point is `(e^{2πix}, kleinU (e^{2πiy}) t)`.
* For a unit map `ν : T² → TotalSpace F V` intertwining the deck map with `v ↦ -v`, the map
  `kleinLensMap ν : L(4, -1) → TotalSpace F V`, `[w] ↦ kleinT u • ν (circleArg z, circleArg u)` on
  model points `(z, u)`, is well defined and smooth off `{w₁² = w₂²}` (`contMDiffAt_kleinLensMap`).
Two points of `S³` off `{w₁² = w₂²}` with equal or deck-related model points have the same image
in `L(4, -1)` (`projection_eq_of_modelPoint`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Module Metric
open scoped Manifold ContDiff Topology ComplexConjugate Real

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.Klein

open GC.Seifert DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
open DifferentialGeometry.Geometry.Collapse.ZeroModel.SpaceForm

universe u

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- `ℝ⁴` has dimension `3 + 1`. -/
local instance finrankFourFact_LFR54QUOT : Fact (finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

/-! ### Model points and the lens projection -/

theorem sq_sub_sq_lensUnitAction {ε : Circle} (hε : ε ^ 4 = 1) (p : ℂ × ℂ) :
    (lensUnitAction ε p).1 ^ 2 - (lensUnitAction ε p).2 ^ 2 =
      (ε : ℂ) ^ 2 * (p.1 ^ 2 - p.2 ^ 2) := by
  obtain ⟨h1, h2⟩ := lensUnitAction_sq hε p
  rw [h1, h2]
  ring

/-- Points of `S³` off `{w₁² = w₂²}` whose model points agree or differ by the deck map have the
same image in `L(4, -1)`. -/
theorem projection_eq_of_modelPoint {x y : S3}
    (hx : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0)
    (hy : (lensPair y).1 ^ 2 - (lensPair y).2 ^ 2 ≠ 0)
    (h : modelPoint (lensPair y) = modelPoint (lensPair x) ∨
      modelPoint (lensPair y) = modelDeck (modelPoint (lensPair x))) :
    mobiusLensGroup.projection x = mobiusLensGroup.projection y := by
  rw [projection_eq_projection_iff]
  have key : ∀ ε : Circle, ε ^ 4 = 1 →
      modelPoint (lensPair y) = modelPoint (lensUnitAction ε (lensPair x)) →
        ∃ ε' : Circle, ε' ^ 4 = 1 ∧ lensPair y = lensUnitAction ε' (lensPair x) := by
    intro ε hε he
    have hn : ‖(lensUnitAction ε (lensPair x)).1‖ ^ 2 +
        ‖(lensUnitAction ε (lensPair x)).2‖ ^ 2 = 1 := by
      simp only [lensUnitAction, norm_mul, Circle.norm_coe, one_mul]
      exact norm_sq_lensPair_sphere x
    have hab : (lensUnitAction ε (lensPair x)).1 ^ 2 -
        (lensUnitAction ε (lensPair x)).2 ^ 2 ≠ 0 := by
      rw [sq_sub_sq_lensUnitAction hε]
      exact mul_ne_zero (pow_ne_zero 2 (Circle.coe_ne_zero ε)) hx
    rcases eq_or_eq_neg_of_modelPoint_eq hn (norm_sq_lensPair_sphere y) hab hy he with h | h
    · exact ⟨ε, hε, h⟩
    · refine ⟨ε * circleI ^ 2, ?_, by rw [lensUnitAction_mul_circleI_sq, h]⟩
      rw [mul_pow, hε, one_mul, ← pow_mul, show 2 * 4 = 4 * 2 from rfl, pow_mul,
        circleI_pow_four, one_pow]
  rcases h with h | h
  · exact key 1 (one_pow _) (by rw [lensUnitAction_one, h])
  · refine key circleI circleI_pow_four ?_
    rw [h, modelPoint_lensUnitAction_of_sq_eq_neg_one (by rw [coe_circleI, Complex.I_sq])]

theorem norm_modelFibrePoint {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    ‖modelFibrePoint p‖ = 1 := by
  rw [modelFibrePoint, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hab)]

theorem modelFibrePoint_ne_zero {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    modelFibrePoint p ≠ 0 := by
  intro h
  have := norm_modelFibrePoint hab
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem modelAnnulusPoint_ne_zero {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    modelAnnulusPoint p ≠ 0 := by
  obtain ⟨h1, h2⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  rw [modelAnnulusPoint]
  exact div_ne_zero (neg_ne_zero.mpr h2) h1

theorem contDiffAt_modelPoint {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    ContDiffAt ℝ ∞ modelPoint p := by
  obtain ⟨h1, -⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  have hd : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.1 ^ 2 - q.2 ^ 2) p :=
    (contDiffAt_fst.pow 2).sub (contDiffAt_snd.pow 2)
  have hnorm : ContDiffAt ℝ ∞ (norm : ℂ → ℝ) (p.1 ^ 2 - p.2 ^ 2) := contDiffAt_norm ℝ hab
  have hn' : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ‖q.1 ^ 2 - q.2 ^ 2‖) p := hnorm.comp p hd
  have hn : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ((‖q.1 ^ 2 - q.2 ^ 2‖ : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hn'
  have hF : ContDiffAt ℝ ∞ modelFibrePoint p := by
    have he : modelFibrePoint = fun q : ℂ × ℂ =>
        (q.1 ^ 2 - q.2 ^ 2) * (((‖q.1 ^ 2 - q.2 ^ 2‖ : ℝ) : ℂ))⁻¹ :=
      funext fun q => div_eq_mul_inv _ _
    rw [he]
    exact hd.mul (hn.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hab)))
  have hA : ContDiffAt ℝ ∞ modelAnnulusPoint p := by
    have he : modelAnnulusPoint = fun q : ℂ × ℂ => -(q.1 + q.2) * (q.1 - q.2)⁻¹ :=
      funext fun q => div_eq_mul_inv _ _
    rw [he]
    exact (contDiffAt_fst.add contDiffAt_snd).neg.mul ((contDiffAt_fst.sub contDiffAt_snd).inv h1)
  exact hF.prodMk hA

/-! ### The parametrisation `T² × ℝ → L(4, -1)` -/

theorem kleinW_mem_sphere (x y t : ℝ) : lensPair.symm (kleinW x y t) ∈ S3 := by
  rw [mem_sphere_zero_iff_norm]
  have h := norm_sq_eq_lensPair (lensPair.symm (kleinW x y t))
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (h.trans (norm_sq_kleinW x y t))

/-- The point of `S³` with coordinates `kleinW`. -/
def kleinSphere (q : (ℝ × ℝ) × ℝ) : S3 :=
  ⟨lensPair.symm (kleinW q.1.1 q.1.2 q.2), kleinW_mem_sphere _ _ _⟩

theorem lensPair_kleinSphere (q : (ℝ × ℝ) × ℝ) :
    lensPair (kleinSphere q) = kleinW q.1.1 q.1.2 q.2 :=
  lensPair.apply_symm_apply _

theorem sq_sub_sq_kleinSphere (q : (ℝ × ℝ) × ℝ) :
    (lensPair (kleinSphere q)).1 ^ 2 - (lensPair (kleinSphere q)).2 ^ 2 ≠ 0 := by
  rw [lensPair_kleinSphere]
  exact kleinW_sq_sub_sq_ne_zero _ _ _

theorem modelPoint_kleinSphere (q : (ℝ × ℝ) × ℝ) :
    modelPoint (lensPair (kleinSphere q)) =
      ((AddCircle.toCircle (q.1.1 : AddCircle (1 : ℝ)) : ℂ),
        kleinU (AddCircle.toCircle (q.1.2 : AddCircle (1 : ℝ))) q.2) := by
  rw [lensPair_kleinSphere, modelPoint_kleinW, coe_toCircle_coe, coe_toCircle_coe]

theorem contMDiff_kleinSphere :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ kleinSphere := by
  have hid : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (ℝ × ℝ) × ℝ) ∞
      (fun q : (ℝ × ℝ) × ℝ => q) :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk_space (contMDiff_snd.comp contMDiff_fst)).prodMk_space
      contMDiff_snd
  have hf : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E4) ∞
      (fun q : (ℝ × ℝ) × ℝ => lensPair.symm (kleinW q.1.1 q.1.2 q.2)) :=
    (lensPair.symm.contDiff.comp contDiff_kleinW).contMDiff.comp hid
  exact hf.codRestrict_sphere fun q => kleinW_mem_sphere _ _ _

/-- A real representative of a point of `ℝ / ℤ`. -/
def addCircleRep (a : AddCircle (1 : ℝ)) : ℝ :=
  Classical.choose (QuotientAddGroup.mk_surjective a)

theorem coe_addCircleRep (a : AddCircle (1 : ℝ)) : ((addCircleRep a : ℝ) : AddCircle (1 : ℝ)) = a :=
  Classical.choose_spec (QuotientAddGroup.mk_surjective a)

/-- The representative point of `S³` over `(p, t) ∈ T² × ℝ`. -/
def kleinRepSphere (q : T2 × ℝ) : S3 :=
  kleinSphere ((addCircleRep q.1.1, addCircleRep q.1.2), q.2)

theorem modelPoint_kleinRepSphere (q : T2 × ℝ) :
    modelPoint (lensPair (kleinRepSphere q)) =
      ((AddCircle.toCircle q.1.1 : ℂ), kleinU (AddCircle.toCircle q.1.2) q.2) := by
  rw [kleinRepSphere, modelPoint_kleinSphere, coe_addCircleRep, coe_addCircleRep]

theorem sq_sub_sq_kleinRepSphere (q : T2 × ℝ) :
    (lensPair (kleinRepSphere q)).1 ^ 2 - (lensPair (kleinRepSphere q)).2 ^ 2 ≠ 0 :=
  sq_sub_sq_kleinSphere _

/-- **The Klein parametrisation** `T² × ℝ → L(4, -1)`. -/
def kleinTheta (q : T2 × ℝ) : mobiusLens.{u}.Carrier :=
  lensUp (mobiusLensGroup.projection (kleinRepSphere q))

theorem kleinTheta_coe (q : (ℝ × ℝ) × ℝ) :
    kleinTheta.{u} (((q.1.1 : AddCircle (1 : ℝ)), (q.1.2 : AddCircle (1 : ℝ))), q.2) =
      lensUp (mobiusLensGroup.projection (kleinSphere q)) := by
  rw [kleinTheta]
  congr 1
  apply projection_eq_of_modelPoint (sq_sub_sq_kleinRepSphere _) (sq_sub_sq_kleinSphere q)
  left
  rw [modelPoint_kleinSphere, modelPoint_kleinRepSphere]

/-- The covering `ℝ² × ℝ → T² × ℝ`. -/
theorem isLocalDiffeomorph_kleinCover :
    IsLocalDiffeomorph ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : (ℝ × ℝ) × ℝ =>
        (((q.1.1 : AddCircle (1 : ℝ)), (q.1.2 : AddCircle (1 : ℝ))), q.2)) :=
  (AddCircle.isLocalDiffeomorph_coe.prodMap AddCircle.isLocalDiffeomorph_coe).prodMap
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph

theorem contMDiff_kleinTheta :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ kleinTheta.{u} := by
  apply isLocalDiffeomorph_kleinCover.contMDiff_of_comp_of_surjective
  · rintro ⟨⟨a, b⟩, t⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
    exact ⟨((x, y), t), rfl⟩
  · have h := contMDiff_lensUp.{u}.comp
      (mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff.comp contMDiff_kleinSphere)
    refine h.congr fun q => ?_
    exact kleinTheta_coe q

theorem toCircle_half :
    AddCircle.toCircle ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = -1 := by
  apply Circle.ext
  rw [coe_toCircle_coe, Circle.coe_exp, Circle.coe_neg, Circle.coe_one]
  rw [show (2 * π * (1 / 2 : ℝ) : ℝ) = π by ring]
  exact Complex.exp_pi_mul_I

/-- **Klein deck invariance** of the parametrisation. -/
theorem kleinTheta_deck (p : T2) (t : ℝ) :
    kleinTheta.{u} ((p.1 + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -p.2), -t) = kleinTheta.{u} (p, t) := by
  rw [kleinTheta, kleinTheta]
  congr 1
  apply projection_eq_of_modelPoint (sq_sub_sq_kleinRepSphere _) (sq_sub_sq_kleinRepSphere _)
  right
  rw [modelPoint_kleinRepSphere, modelPoint_kleinRepSphere, modelDeck]
  dsimp only
  rw [AddCircle.toCircle_add, toCircle_half, mul_neg_one, AddCircle.toCircle_neg,
    Circle.coe_inv_eq_conj, kleinU_conj_neg (Circle.norm_coe _), Circle.coe_neg, neg_neg,
    inv_inv]

theorem mobiusBundleFunction_lensUp (x : S3) :
    mobiusBundleFunction.{u} (lensUp (mobiusLensGroup.projection x)) =
      bundleQuartic (lensPair x) := rfl

/-- `kleinTheta (p, t)` lies in the twisted `I`-bundle `{Q ≤ 0}` exactly when `|t| ≤ 1`. -/
theorem mobiusBundleFunction_kleinTheta_nonpos_iff {q : T2 × ℝ} :
    mobiusBundleFunction.{u} (kleinTheta q) ≤ 0 ↔ |q.2| ≤ 1 := by
  rw [kleinTheta, mobiusBundleFunction_lensUp,
    bundleQuartic_nonpos_iff (sq_sub_sq_kleinRepSphere q),
    ← joukowski_modelAnnulusPoint (sq_sub_sq_kleinRepSphere q)]
  have hA : modelAnnulusPoint (lensPair (kleinRepSphere q)) =
      kleinU (AddCircle.toCircle q.1.2) q.2 :=
    congrArg Prod.snd (modelPoint_kleinRepSphere q)
  rw [hA, norm_joukowski_le_three_iff (kleinU_ne_zero (Circle.coe_ne_zero _) q.2),
    kleinT_kleinU (Circle.norm_coe _)]

/-! ### The inverse map `L(4, -1) → TotalSpace F V` -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The Klein deck map `(x, y) ↦ (x + ½, -y)` of the torus. -/
def kleinDeck (p : T2) : T2 := (p.1 + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -p.2)

/-- On model points `(z, u)`: `kleinT u • ν (circleArg z, circleArg u)`. -/
def kleinCoordMap (ν : T2 → TotalSpace F V) (m : ℂ × ℂ) : TotalSpace F V :=
  rankOneParam ν ((circleArg m.1, circleArg m.2), kleinT m.2)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem kleinCoordMap_deck (ν : T2 → TotalSpace F V)
    (hνneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩) {m : ℂ × ℂ} (h1 : m.1 ≠ 0)
    (h2 : m.2 ≠ 0) : kleinCoordMap ν (modelDeck m) = kleinCoordMap ν m := by
  rw [kleinCoordMap, kleinCoordMap, modelDeck]
  dsimp only
  rw [circleArg_neg h1, circleArg_inv h2, kleinT_inv]
  exact rankOneParam_deck ν kleinDeck hνneg (circleArg m.1, circleArg m.2) (kleinT m.2)

/-- The map on `S³` (a constant off the model region). -/
def kleinSphereMap (ν : T2 → TotalSpace F V) (x : S3) : TotalSpace F V :=
  if (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 = 0 then ν (0, 0)
  else kleinCoordMap ν (modelPoint (lensPair x))

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem kleinSphereMap_of_ne (ν : T2 → TotalSpace F V) {x : S3}
    (hx : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0) :
    kleinSphereMap ν x = kleinCoordMap ν (modelPoint (lensPair x)) := by
  rw [kleinSphereMap, ite_eq_right hx]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem kleinSphereMap_invariant (ν : T2 → TotalSpace F V)
    (hνneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩) (x y : S3)
    (h : mobiusLensGroup.projection x = mobiusLensGroup.projection y) :
    kleinSphereMap ν x = kleinSphereMap ν y := by
  obtain ⟨ε, hε, hy⟩ := (projection_eq_projection_iff x y).mp h
  have hab : (lensPair y).1 ^ 2 - (lensPair y).2 ^ 2 =
      (ε : ℂ) ^ 2 * ((lensPair x).1 ^ 2 - (lensPair x).2 ^ 2) := by
    rw [hy, sq_sub_sq_lensUnitAction hε]
  by_cases hx0 : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 = 0
  · have hy0 : (lensPair y).1 ^ 2 - (lensPair y).2 ^ 2 = 0 := by rw [hab, hx0, mul_zero]
    rw [kleinSphereMap, kleinSphereMap, ite_eq_left hx0, ite_eq_left hy0]
  · have hy0 : (lensPair y).1 ^ 2 - (lensPair y).2 ^ 2 ≠ 0 := by
      rw [hab]
      exact mul_ne_zero (pow_ne_zero 2 (Circle.coe_ne_zero ε)) hx0
    rw [kleinSphereMap_of_ne ν hx0, kleinSphereMap_of_ne ν hy0, hy]
    rcases sq_eq_one_or_neg_one hε with h2 | h2
    · rw [modelPoint_lensUnitAction_of_sq_eq_one h2]
    · rw [modelPoint_lensUnitAction_of_sq_eq_neg_one h2,
        kleinCoordMap_deck ν hνneg (modelFibrePoint_ne_zero hx0) (modelAnnulusPoint_ne_zero hx0)]

/-- **The inverse map** `L(4, -1) → TotalSpace F V`. -/
def kleinLensMap (ν : T2 → TotalSpace F V)
    (hνneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩) (y : mobiusLens.{u}.Carrier) :
    TotalSpace F V :=
  orbitLift mobiusLensGroup (kleinSphereMap ν) (kleinSphereMap_invariant ν hνneg) (lensDown y)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem kleinLensMap_lensUp (ν : T2 → TotalSpace F V)
    (hνneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩) (x : S3) :
    kleinLensMap.{u} ν hνneg (lensUp (mobiusLensGroup.projection x)) = kleinSphereMap ν x := rfl

theorem contMDiffAt_kleinT {u : ℂ} (hu : u ≠ 0) : ContDiffAt ℝ ∞ kleinT u := by
  have hs : ContDiff ℝ ∞ (fun v : ℂ => Complex.normSq v) := by
    have he : (fun v : ℂ => Complex.normSq v) = fun v => ‖v‖ ^ 2 :=
      funext Complex.normSq_eq_norm_sq
    rw [he]
    exact contDiff_norm_sq ℝ
  have hs0 : Complex.normSq u ≠ 0 := (Complex.normSq_pos.mpr hu).ne'
  have hC : ContDiffAt ℝ ∞ kleinC u :=
    contDiffAt_const.sub ((Complex.reCLM.contDiff.comp (contDiff_id.pow 2)).contDiffAt.div
      hs.contDiffAt hs0)
  have hsq : ContDiffAt ℝ ∞ (fun v : ℂ => √(kleinC v ^ 2 - 1)) u :=
    ((hC.pow 2).sub contDiffAt_const).sqrt (kleinC_sq_sub_one_pos u).ne'
  exact (hs.contDiffAt.sub (hs.contDiffAt.inv hs0)).div (contDiffAt_const.mul hsq)
    (mul_ne_zero two_ne_zero (sqrt_kleinC_pos u).ne')

theorem contMDiffAt_kleinCoordMap (ν : T2 → TotalSpace F V)
    (hν : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (IB.prod 𝓘(ℝ, F)) ∞ ν) {m : ℂ × ℂ}
    (h1 : m.1 ≠ 0) (h2 : m.2 ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ × ℂ) (IB.prod 𝓘(ℝ, F)) ∞ (kleinCoordMap ν) m := by
  have ha1 : ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℝ) ∞ (fun m : ℂ × ℂ => circleArg m.1) m :=
    (contMDiffAt_circleArg h1).comp m contDiffAt_fst.contMDiffAt
  have ha2 : ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℝ) ∞ (fun m : ℂ × ℂ => circleArg m.2) m :=
    (contMDiffAt_circleArg h2).comp m contDiffAt_snd.contMDiffAt
  have hT : ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℝ) ∞ (fun m : ℂ × ℂ => kleinT m.2) m :=
    ((contMDiffAt_kleinT h2).comp m contDiffAt_snd).contMDiffAt
  have hνm : ContMDiffAt 𝓘(ℝ, ℂ × ℂ) (IB.prod 𝓘(ℝ, F)) ∞
      (fun m : ℂ × ℂ => ν (circleArg m.1, circleArg m.2)) m :=
    (hν _).comp m (ha1.prodMk ha2)
  exact (DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul _).comp m (hT.prodMk hνm)

theorem contMDiffAt_kleinSphereMap (ν : T2 → TotalSpace F V)
    (hν : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (IB.prod 𝓘(ℝ, F)) ∞ ν) {x : S3}
    (hx : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0) :
    ContMDiffAt (𝓡 3) (IB.prod 𝓘(ℝ, F)) ∞ (kleinSphereMap ν) x := by
  have hp : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun x : S3 => modelPoint (lensPair x)) x :=
    ((contDiffAt_modelPoint hx).comp _ lensPair.contDiff.contDiffAt).contMDiffAt.comp x
      (contMDiff_coe_sphere x)
  have hc := (contMDiffAt_kleinCoordMap ν hν (modelFibrePoint_ne_zero hx)
    (modelAnnulusPoint_ne_zero hx)).comp x hp
  apply hc.congr_of_eventuallyEq
  have hcont : Continuous fun x : S3 => (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 := by
    have : Continuous fun x : S3 => lensPair (x : E4) :=
      lensPair.continuous.comp continuous_subtype_val
    exact (continuous_fst.comp this).pow 2 |>.sub ((continuous_snd.comp this).pow 2)
  filter_upwards [hcont.continuousAt.eventually_ne hx] with x' hx'
  exact kleinSphereMap_of_ne ν hx'

theorem contMDiffAt_kleinLensMap (ν : T2 → TotalSpace F V)
    (hν : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (IB.prod 𝓘(ℝ, F)) ∞ ν)
    (hνneg : ∀ p, ν (kleinDeck p) = ⟨(ν p).proj, -(ν p).2⟩) {x : S3}
    (hx : (lensPair x).1 ^ 2 - (lensPair x).2 ^ 2 ≠ 0) :
    ContMDiffAt (𝓡 3) (IB.prod 𝓘(ℝ, F)) ∞ (kleinLensMap.{u} ν hνneg)
      (lensUp (mobiusLensGroup.projection x)) := by
  have h := contMDiffAt_orbitLift mobiusLensGroup (kleinSphereMap ν)
    (kleinSphereMap_invariant ν hνneg) x (contMDiffAt_kleinSphereMap ν hν hx)
  exact ContMDiffAt.comp (g := orbitLift mobiusLensGroup (kleinSphereMap ν)
    (kleinSphereMap_invariant ν hνneg)) (f := lensDown.{u})
    (lensUp (mobiusLensGroup.projection x)) h (contMDiff_lensDown.{u} _)

end DifferentialGeometry.Geometry.Collapse.ZeroModel.Klein
