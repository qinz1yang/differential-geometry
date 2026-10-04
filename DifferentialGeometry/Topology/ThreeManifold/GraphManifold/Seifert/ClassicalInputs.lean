import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Slope

/-!
# Classical inputs for Seifert pieces

Chapter 6, packet K08. Proved: `linearTorusDiffeomorph A`, `(u, v) ↦ (u ^ a v ^ b, u ^ c v ^ d)`
for `A = !![a, b; c, d] : GL (Fin 2) ℤ`; `IsotopicDiffeomorph` (smooth isotopy through
diffeomorphisms) is an equivalence relation, and isotopic diffeomorphisms of `Torus` have the same
`torusMatrix`, so act equally on `PrimitiveSlope` and preserve `delta`. Named inputs:
`TorusMatrixLinear` (the matrix of `linearTorusDiffeomorph A` is `A`); `TorusMappingClassLinear`
(every `φ` is isotopic to `linearTorusDiffeomorph (torusUnit φ)`, so isotopy is equality of
matrices); RG01 `CircleBundlesOverElementarySurfacesStandard` (a circle fibration of an oriented
carrier over a disc, annulus or pants is a product over the base; over a Möbius band it is
`(S¹ × I × S¹) / ((z, t, v) ∼ (-z, 1 - t, v⁻¹))`); RG03 `CollaredSurfaceDecomposition` (every
compact surface is glued from embedded elementary pieces along boundary circles) and
`ExistsEssentialCurveOrArc` (if π₁ has an element of infinite order). Models: `discModel`,
`annulusModel`, `pantsModel` in `ℂ`, `mobiusModel` in `ℝ³`, reached by `IsModelEmbedding`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.Seifert
universe u

theorem contMDiff_circle_zpow (n : ℤ) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ n) := by
  cases n with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using contMDiff_pow k
  | negSucc k => simpa only [zpow_negSucc] using (contMDiff_pow (k + 1)).inv

def linearTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Torus) : Torus :=
  (x.1 ^ A 0 0 * x.2 ^ A 0 1, x.1 ^ A 1 0 * x.2 ^ A 1 1)

theorem contMDiff_linearTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ContMDiff torusModel torusModel ∞ (linearTorusMap A) :=
  (((contMDiff_circle_zpow _).comp contMDiff_fst).mul ((contMDiff_circle_zpow _).comp
    contMDiff_snd)).prodMk (((contMDiff_circle_zpow _).comp contMDiff_fst).mul
    ((contMDiff_circle_zpow _).comp contMDiff_snd))

theorem linearTorusMap_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (x : Torus) :
    linearTorusMap (A * B) x = linearTorusMap A (linearTorusMap B x) := by
  obtain ⟨u, v⟩ := x
  simp only [linearTorusMap, Matrix.mul_apply, Fin.sum_univ_two, mul_zpow, ← zpow_mul, zpow_add]
  refine Prod.ext ?_ ?_ <;>
    simp only [mul_comm (B _ _) (A _ _)] <;> exact mul_mul_mul_comm _ _ _ _

theorem linearTorusMap_one (x : Torus) : linearTorusMap 1 x = x := by
  simp [linearTorusMap]

def linearTorusDiffeomorph (A : GL (Fin 2) ℤ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus where
  toFun := linearTorusMap A
  invFun := linearTorusMap ↑A⁻¹
  left_inv x := by rw [← linearTorusMap_mul, Units.inv_mul, linearTorusMap_one]
  right_inv x := by rw [← linearTorusMap_mul, Units.mul_inv, linearTorusMap_one]
  contMDiff_toFun := contMDiff_linearTorusMap A
  contMDiff_invFun := contMDiff_linearTorusMap _

theorem linearTorusDiffeomorph_torusBase (A : GL (Fin 2) ℤ) :
    linearTorusDiffeomorph A torusBase = torusBase := by
  change linearTorusMap A torusBase = torusBase
  simp [linearTorusMap]

theorem linearTorusDiffeomorph_mul (A B : GL (Fin 2) ℤ) :
    linearTorusDiffeomorph (A * B) = (linearTorusDiffeomorph B).trans (linearTorusDiffeomorph A) :=
  Diffeomorph.ext fun x => linearTorusMap_mul A B x

section Isotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def IsotopicDiffeomorph (φ ψ : M ≃ₘ⟮I, I⟯ M) : Prop :=
  ∃ F : ℝ → M ≃ₘ⟮I, I⟯ M,
    ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M => F q.1 q.2) ∧
    ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M => (F q.1).symm q.2) ∧ F 0 = φ ∧ F 1 = ψ

namespace IsotopicDiffeomorph

theorem refl (φ : M ≃ₘ⟮I, I⟯ M) : IsotopicDiffeomorph φ φ :=
  ⟨fun _ => φ, φ.contMDiff.comp contMDiff_snd, φ.symm.contMDiff.comp contMDiff_snd, rfl, rfl⟩

theorem symm {φ ψ : M ≃ₘ⟮I, I⟯ M} (h : IsotopicDiffeomorph φ ψ) : IsotopicDiffeomorph ψ φ := by
  obtain ⟨F, hF, hF', h0, h1⟩ := h
  have hr : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞ (fun q : ℝ × M => (1 - q.1, q.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  exact ⟨fun t => F (1 - t), hF.comp hr, hF'.comp hr, by simpa using h1, by simpa using h0⟩

theorem trans {φ ψ χ : M ≃ₘ⟮I, I⟯ M} (h : IsotopicDiffeomorph φ ψ)
    (h' : IsotopicDiffeomorph ψ χ) : IsotopicDiffeomorph φ χ := by
  obtain ⟨F, hF, hF', h0, h1⟩ := h
  obtain ⟨G, hG, hG', h0', h1'⟩ := h'
  refine ⟨fun t => (F t).trans (ψ.symm.trans (G t)),
    hG.comp (contMDiff_fst.prodMk (ψ.symm.contMDiff.comp hF)),
    hF'.comp (contMDiff_fst.prodMk (ψ.contMDiff.comp hG')), ?_, ?_⟩ <;>
    ext x <;> simp [h0, h1, h0', h1']

end IsotopicDiffeomorph

end Isotopy

private theorem changeBasepoint_trans {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ : Path x y) (δ : Path y z) (g : FundamentalGroup X z) :
    fundamentalGroupChangeBasepoint (γ.trans δ) g =
      fundamentalGroupChangeBasepoint γ (fundamentalGroupChangeBasepoint δ g) := by
  have hq : ∀ {a b : X} (q : Path a b),
      (⟦q⟧ : Path.Homotopic.Quotient a b) = Path.Homotopic.Quotient.mk q := fun _ => rfl
  simp only [fundamentalGroupChangeBasepoint_apply, hq, ← Path.Homotopic.Quotient.mk_symm,
    Path.trans_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

theorem torusAut_eq_of_homotopy {f g : C(Torus, Torus)} (F : f.Homotopy g) :
    torusAut f = torusAut g := by
  refine MonoidHom.ext fun p => ?_
  rw [torusAut_eq g ((PathConnectedSpace.somePath torusBase (f torusBase)).trans
    (F.evalAt torusBase))]
  change fundamentalGroupChangeBasepoint _ (FundamentalGroup.map f torusBase p) =
    fundamentalGroupChangeBasepoint _ (FundamentalGroup.map g torusBase p)
  rw [changeBasepoint_trans, ← GC.Topology.homotopy_track f g F torusBase]
  rfl

theorem torusMatrix_eq_of_isotopic {φ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    (h : IsotopicDiffeomorph φ ψ) : torusMatrix φ = torusMatrix ψ := by
  obtain ⟨F, hF, -, h0, h1⟩ := h
  rw [torusMatrix, torusMatrix, torusMapMatrix, torusMapMatrix, torusAut_eq_of_homotopy
    (g := ⟨ψ, ψ.continuous⟩)
    { toFun := fun p : unitInterval × Torus => F p.1 p.2
      continuous_toFun := hF.continuous.comp (continuous_subtype_val.prodMap continuous_id)
      map_zero_left := fun x => by simp [h0]
      map_one_left := fun x => by simp [h1] }]

theorem torusUnit_eq_of_isotopic {φ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    (h : IsotopicDiffeomorph φ ψ) : torusUnit φ = torusUnit ψ :=
  Units.ext (torusMatrix_eq_of_isotopic h)

theorem delta_smul_of_isotopic {φ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus}
    (h : IsotopicDiffeomorph φ ψ) (a b : PrimitiveSlope) :
    PrimitiveSlope.delta (torusUnit φ • a) (torusUnit ψ • b) = PrimitiveSlope.delta a b := by
  rw [torusUnit_eq_of_isotopic h, PrimitiveSlope.delta_smul]

def TorusMatrixLinear : Prop :=
  ∀ A : GL (Fin 2) ℤ, torusMatrix (linearTorusDiffeomorph A) = A

def TorusMappingClassLinear : Prop :=
  ∀ φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus,
    IsotopicDiffeomorph φ (linearTorusDiffeomorph (torusUnit φ))

theorem torusUnit_surjective (h : TorusMatrixLinear) : Function.Surjective torusUnit :=
  fun A => ⟨linearTorusDiffeomorph A, Units.ext (h A)⟩

theorem isotopic_iff_torusMatrix_eq (h : TorusMappingClassLinear)
    {φ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus} :
    IsotopicDiffeomorph φ ψ ↔ torusMatrix φ = torusMatrix ψ := by
  refine ⟨torusMatrix_eq_of_isotopic, fun hm => ?_⟩
  have hu : torusUnit φ = torusUnit ψ := Units.ext hm
  exact (h φ).trans (hu ▸ (h ψ).symm)

def discModel : Set ℂ := {z | ‖z‖ ≤ 1}

def annulusModel : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}

def pantsModel : Set ℂ := {z | ‖z‖ ≤ 4 ∧ 1 ≤ ‖z - 2‖ ∧ 1 ≤ ‖z + 2‖}

def mobiusPoint (z : Circle) (t : unitInterval) : EuclideanSpace ℝ (Fin 3) :=
  !₂[(2 + (2 * t - 1) * (z : ℂ).re) * ((z : ℂ) ^ 2).re,
    (2 + (2 * t - 1) * (z : ℂ).re) * ((z : ℂ) ^ 2).im, (2 * t - 1) * (z : ℂ).im]

def mobiusModel : Set (EuclideanSpace ℝ (Fin 3)) := Set.range (Function.uncurry mobiusPoint)

def mobiusDeck (p : (Circle × unitInterval) × Circle) : (Circle × unitInterval) × Circle :=
  ((-p.1.1, unitInterval.symm p.1.2), p.2⁻¹)

def IsModelEmbedding {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (B : CompactSurface.{u})
    (e : B.Carrier → F) (S : Set F) : Prop :=
  ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, F) ∞ e ∧ Function.Injective e ∧
    (∀ x, Function.Injective (mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, F) e x)) ∧
    Set.range e = S

def IsPlanarElementary (B : CompactSurface.{u}) : Prop :=
  ∃ e : B.Carrier → ℂ, IsModelEmbedding B e discModel ∨ IsModelEmbedding B e annulusModel ∨
    IsModelEmbedding B e pantsModel

def IsElementarySurface (B : CompactSurface.{u}) : Prop :=
  IsPlanarElementary B ∨
    ∃ e : B.Carrier → EuclideanSpace ℝ (Fin 3), IsModelEmbedding B e mobiusModel

def IsTwistedChart {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
    (F : CircleFibration C U) (e : F.base.Carrier → EuclideanSpace ℝ (Fin 3))
    (Ψ : (Circle × unitInterval) × Circle → U) : Prop :=
  ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) C.model ∞ Ψ ∧ Function.Surjective Ψ ∧
    (∀ p q, Ψ p = Ψ q ↔ q = p ∨ q = mobiusDeck p) ∧
    (∀ p, Function.Injective (mfderiv (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) C.model Ψ p)) ∧
    ∀ p, e (F.projection (Ψ p)) = mobiusPoint p.1.1 p.1.2

def CircleBundlesOverElementarySurfacesStandard : Prop :=
  ∀ (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier) (F : CircleFibration C U),
    (IsPlanarElementary F.base →
      ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle,
        ∀ x, (Φ x).1 = F.projection x) ∧
    ∀ e : F.base.Carrier → EuclideanSpace ℝ (Fin 3), IsModelEmbedding F.base e mobiusModel →
      ∃ Ψ : (Circle × unitInterval) × Circle → U, IsTwistedChart F e Ψ

structure ElementaryDecomposition (B : CompactSurface.{u}) where
  count : ℕ
  piece : Fin count → CompactSurface.{u}
  elementary : ∀ j, IsElementarySurface (piece j)
  inclusion : (j : Fin count) → (piece j).Carrier → B.Carrier
  smooth : ∀ j, ContMDiff (SurfaceModel.model (piece j).kind) (SurfaceModel.model B.kind) ∞
    (inclusion j)
  immersion : ∀ j x, Function.Injective
    (mfderiv (SurfaceModel.model (piece j).kind) (SurfaceModel.model B.kind) (inclusion j) x)
  injective : ∀ j, Function.Injective (inclusion j)
  covers : ∀ b, ∃ j x, inclusion j x = b
  glued : ∀ j k x y, j ≠ k → inclusion j x = inclusion k y →
    (SurfaceModel.model (piece j).kind).IsBoundaryPoint x ∧
      (SurfaceModel.model (piece k).kind).IsBoundaryPoint y ∧
      (SurfaceModel.model B.kind).IsInteriorPoint (inclusion j x)
  at_most_two : ∀ j k l x y z, inclusion j x = inclusion k y → inclusion k y = inclusion l z →
    j = k ∨ k = l ∨ j = l

def CollaredSurfaceDecomposition : Prop :=
  ∀ B : CompactSurface.{u}, Nonempty (ElementaryDecomposition B)

def IsEssentialCurve (B : CompactSurface.{u})
    (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
      B.Carrier ∞) : Prop :=
  c.source = {p | -1 < p.2 ∧ p.2 < 1} ∧ c.target ⊆ (SurfaceModel.model B.kind).interior B.Carrier ∧
    ∃ γ : C(Circle, B.Carrier), (∀ z, γ z = c (z, 0)) ∧
      Function.Injective (FundamentalGroup.map γ 1) ∧
      ∀ δ : C(Circle, B.Carrier), (∀ z, (SurfaceModel.model B.kind).IsBoundaryPoint (δ z)) →
        ¬ γ.Homotopic δ

def IsEssentialArc (B : CompactSurface.{u}) (a : unitInterval → B.Carrier) : Prop :=
  ContMDiff (𝓡∂ 1) (SurfaceModel.model B.kind) ∞ a ∧ Function.Injective a ∧
    (∀ t, Function.Injective (mfderiv (𝓡∂ 1) (SurfaceModel.model B.kind) a t)) ∧
    (∀ t, (SurfaceModel.model B.kind).IsBoundaryPoint (a t) ↔ t = 0 ∨ t = 1) ∧
    ∀ α δ : Path (a 0) (a 1), ⇑α = a →
      (∀ t, (SurfaceModel.model B.kind).IsBoundaryPoint (δ t)) → ¬ α.Homotopic δ

def ExistsEssentialCurveOrArc : Prop :=
  ∀ (B : CompactSurface.{u}) (b : B.Carrier),
    (∃ g : FundamentalGroup B.Carrier b, ¬ IsOfFinOrder g) →
      (∃ c, IsEssentialCurve B c) ∨ ∃ a, IsEssentialArc B a

end GC.Seifert
