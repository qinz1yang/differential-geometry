import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Adapters
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverAnnulus

/-!
# Torus mapping classes: reduction, lifts, fibre-preserving maps

Chapter 6, packet K08, lane MC0 of the `TorusMappingClassLinear` programme
(`docs/geometrization/handoffs/20261004-survey-torus-mapping-class.md`, corrected by review 12).

Common vocabulary: `TDiff` (diffeomorphisms of `Torus`), `torusRefl`, the axes `alphaCircle`,
`betaCircle`, `heightOnCircle φ z = (φ (z, 1)).2`, and the covering
`torusCover (x, y) = (exp 2πix, exp 2πiy)`, a surjective local diffeomorphism and an open quotient
map, with the section `torusSection`.

(1) Reduction. `torusMappingClassLinear_of_isotopic_refl`: if every `φ` with `torusMatrix φ = 1` is
isotopic to the identity, then `TorusMappingClassLinear` (compose with `L⁻¹`, `L` linear).

(2) Lift dictionary. Every `φ` has a smooth lift `Φ : ℝ² → ℝ²` (`exists_torusLift`); for ANY
continuous lift the deck translations are the columns of `torusMatrix φ`, in the column/`mulVec`
convention of `Slope` and `Adapters`: `Φ (p + (m, n)) = Φ p + A (m, n)` (`torusLift_add_int`).
The matrix is identified by the straight-line homotopy from `Φ` to the linear map `A`, which
descends to a homotopy from `φ` to `Circle.matrixContinuousMap A`. Lifts are unique up to `ℤ²`
(`exists_int_of_torusCover_eq`, `eq_of_torusCover_eq`); a lift can be normalised to take a
prescribed value at a chosen point (`exists_torusLift_apply_eq`); no lift is asked to fix `0`.
The normalised lift is a global diffeomorphism of `ℝ²` whose inverse lifts `φ.symm`
(`exists_torusLiftDiffeomorph`): the composite of the two lifts lifts the identity and agrees with
it at one point.

(3) Isotopies from lifts. `torusFamily` descends a jointly smooth family `G` on `ℝ × ℝ²`, with a
jointly smooth inverse family `Ginv`, both `ℤ²`-periodic modulo `ℤ²`, to a family of torus
diffeomorphisms; `isotopicDiffeomorph_of_lift` turns it into `IsotopicDiffeomorph` (the parameter
ranges over all of `ℝ`, the inverse is jointly smooth by construction).

(4) Easy layer. If `(φ (u, v)).1` does not depend on `v`, then `φ` lifts to
`(x, y) ↦ (a x, b (x, y))` with `A 0 1 = 0`, `A 0 0, A 1 1 ∈ {±1}`, and `A 0 0 · a' > 0`,
`A 1 1 · ∂_y b > 0` everywhere: the base map and every fibre map are circle diffeomorphisms, of
either degree sign (`exists_fibrePreserving_lift`; the signs come from the invertibility of the
Jacobian of the global lift). The straight lines `(1 - τ) a + τ A₀₀ x` and
`(1 - τ) b + τ (A₁₀ x + A₁₁ y)`, `τ = cutoff 0 1 t`, keep both signs; their inverses are
parametrised inverses of one-variable families (`exists_contDiff_inverse_of_sign`). This gives
`isotopicDiffeomorph_linear_of_fst_eq`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

abbrev TDiff := Torus ≃ₘ⟮torusModel, torusModel⟯ Torus

abbrev torusRefl : TDiff := Diffeomorph.refl torusModel Torus ∞

def alphaCircle (z : Circle) : Torus := (z, 1)

def betaCircle (w : Circle) : Torus := (1, w)

def heightOnCircle (φ : TDiff) (z : Circle) : Circle := (φ (alphaCircle z)).2

theorem torusMappingClassLinear_of_isotopic_refl
    (h : ∀ φ : TDiff, torusMatrix φ = 1 → IsotopicDiffeomorph φ torusRefl) :
    TorusMappingClassLinear := by
  intro φ
  set L := linearTorusDiffeomorph (torusUnit φ)
  have hL : torusMatrix L.symm * torusMatrix φ = 1 := by
    have hu : torusUnit L = torusUnit φ := torusUnit_linearTorusDiffeomorph _
    have h1 : torusMatrix L.symm = ((torusUnit L)⁻¹ : GL (Fin 2) ℤ) := rfl
    rw [h1, hu, ← val_torusUnit φ, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨F, hF, hF', h0, h1⟩ := h (φ.trans L.symm) (by rw [torusMatrix_trans]; exact hL)
  refine ⟨fun t => (F t).trans L, L.contMDiff.comp hF, hF'.comp
    (contMDiff_fst.prodMk (L.symm.contMDiff.comp contMDiff_snd)), ?_, ?_⟩
  · change (F 0).trans L = φ
    rw [h0]; exact Diffeomorph.ext fun x => L.apply_symm_apply (φ x)
  · change (F 1).trans L = L
    rw [h1]; exact Diffeomorph.ext fun x => rfl

def torusCover (p : ℝ × ℝ) : Torus :=
  (Circle.exp (2 * Real.pi * p.1), Circle.exp (2 * Real.pi * p.2))

theorem torusCover_eq (p : ℝ × ℝ) : torusCover p = (cexp p.1, cexp p.2) := by
  rw [cexp_eq, cexp_eq]
  rfl

theorem torusCover_add_int (p : ℝ × ℝ) (m n : ℤ) :
    torusCover (p.1 + m, p.2 + n) = torusCover p := by
  rw [torusCover_eq, torusCover_eq, cexp_add_int, cexp_add_int]

theorem torusCover_eq_torusCover_iff {p q : ℝ × ℝ} :
    torusCover p = torusCover q ↔ ∃ m n : ℤ, p = (q.1 + m, q.2 + n) := by
  rw [torusCover_eq, torusCover_eq, Prod.mk.injEq, cexp_eq_cexp_iff, cexp_eq_cexp_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    exact ⟨m, n, Prod.ext hm hn⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩

theorem torusCover_surjective : Function.Surjective torusCover := by
  rintro ⟨u, v⟩
  obtain ⟨a, rfl⟩ := cexp_surjective u
  obtain ⟨b, rfl⟩ := cexp_surjective v
  exact ⟨(a, b), torusCover_eq (a, b)⟩

theorem torusCover_zero : torusCover 0 = torusBase := by
  rw [torusCover_eq]
  exact Prod.ext cexp_zero cexp_zero

def planeModelEquiv : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (ℝ × ℝ) where
  toEquiv := Equiv.refl _
  contMDiff_toFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  contMDiff_invFun := contMDiff_fst.prodMk_space contMDiff_snd

theorem isLocalDiffeomorph_torusCover :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ × ℝ) torusModel ∞ torusCover := by
  have h : torusCover = Prod.map cexp cexp ∘ planeModelEquiv := by
    funext p
    exact torusCover_eq p
  rw [h]
  exact DifferentialGeometry.isLocalDiffeomorph_comp
    (isLocalDiffeomorph_cexp.prodMap isLocalDiffeomorph_cexp)
    planeModelEquiv.isLocalDiffeomorph

theorem contMDiff_torusCover : ContMDiff 𝓘(ℝ, ℝ × ℝ) torusModel ∞ torusCover :=
  isLocalDiffeomorph_torusCover.contMDiff

theorem continuous_torusCover : Continuous torusCover :=
  contMDiff_torusCover.continuous

theorem linearTorusMap_torusCover (A : Matrix (Fin 2) (Fin 2) ℤ) (p : ℝ × ℝ) :
    linearTorusMap A (torusCover p) =
      torusCover (A 0 0 * p.1 + A 0 1 * p.2, A 1 0 * p.1 + A 1 1 * p.2) := by
  simp only [linearTorusMap, torusCover, mul_add, Circle.exp_add]
  refine Prod.ext ?_ ?_ <;> simp only <;>
    rw [mul_left_comm _ ((A _ _ : ℤ) : ℝ), mul_left_comm _ ((A _ _ : ℤ) : ℝ),
      Circle.exp_intCast_mul, Circle.exp_intCast_mul]

theorem exists_int_of_torusCover_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {F F' : A → ℝ × ℝ} (hF : Continuous F) (hF' : Continuous F')
    (h : ∀ a, torusCover (F' a) = torusCover (F a)) (a₀ : A) :
    ∃ m n : ℤ, ∀ a, F' a = ((F a).1 + m, (F a).2 + n) := by
  have h1 (a : A) : cexp (F' a).1 = cexp (F a).1 := by
    have := congrArg Prod.fst (h a)
    rwa [torusCover_eq, torusCover_eq] at this
  have h2 (a : A) : cexp (F' a).2 = cexp (F a).2 := by
    have := congrArg Prod.snd (h a)
    rwa [torusCover_eq, torusCover_eq] at this
  obtain ⟨m, hm⟩ := exists_int_of_cexp_eq hF.fst hF'.fst h1 a₀
  obtain ⟨n, hn⟩ := exists_int_of_cexp_eq hF.snd hF'.snd h2 a₀
  exact ⟨m, n, fun a => Prod.ext (hm a) (hn a)⟩

def torusSection (z : Torus) : ℝ × ℝ := (rep z.1, rep z.2)

theorem torusCover_torusSection (z : Torus) : torusCover (torusSection z) = z := by
  rw [torusCover_eq, torusSection, cexp_rep, cexp_rep]

theorem exists_torusSection_torusCover (p : ℝ × ℝ) :
    ∃ m n : ℤ, torusSection (torusCover p) = (p.1 + m, p.2 + n) :=
  torusCover_eq_torusCover_iff.mp (torusCover_torusSection (torusCover p))

theorem isOpenQuotientMap_torusCover : IsOpenQuotientMap torusCover :=
  ⟨torusCover_surjective, continuous_torusCover, isLocalDiffeomorph_torusCover.isOpenMap⟩

section Lift

variable {φ : TDiff} {Φ : ℝ × ℝ → ℝ × ℝ}

theorem exists_torusLift_shift (hΦ : Continuous Φ)
    (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p)) (m n : ℤ) :
    ∃ a b : ℤ, ∀ p : ℝ × ℝ, Φ (p.1 + m, p.2 + n) = ((Φ p).1 + a, (Φ p).2 + b) :=
  exists_int_of_torusCover_eq hΦ
    (hΦ.comp ((continuous_fst.add continuous_const).prodMk (continuous_snd.add continuous_const)))
    (fun p => by rw [← hlift, ← hlift, torusCover_add_int]) 0

theorem exists_matrix_torusLift (hΦ : Continuous Φ)
    (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p)) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, ∀ (p : ℝ × ℝ) (m n : ℤ),
      Φ (p.1 + m, p.2 + n) =
        ((Φ p).1 + ((A 0 0 * m + A 0 1 * n : ℤ) : ℝ),
          (Φ p).2 + ((A 1 0 * m + A 1 1 * n : ℤ) : ℝ)) := by
  let s : ℤ × ℤ → ℝ × ℝ := fun k => Φ (k.1, k.2) - Φ 0
  have hs (p : ℝ × ℝ) (k : ℤ × ℤ) : Φ (p.1 + k.1, p.2 + k.2) = Φ p + s k := by
    obtain ⟨a, b, hab⟩ := exists_torusLift_shift hΦ hlift k.1 k.2
    have h0 := hab 0
    simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at h0
    simp only [s, h0, hab p]
    exact Prod.ext (by simp) (by simp)
  have hadd (k k' : ℤ × ℤ) : s (k + k') = s k + s k' := by
    have h := hs ((k.1 : ℝ), (k.2 : ℝ)) k'
    simp only at h
    simp only [s, Prod.fst_add, Prod.snd_add, Int.cast_add, h]
    abel
  let σ : ℤ × ℤ →+ ℝ × ℝ := AddMonoidHom.mk' s hadd
  have hint (k : ℤ × ℤ) : ∃ a b : ℤ, s k = ((a : ℝ), (b : ℝ)) := by
    obtain ⟨a, b, hab⟩ := exists_torusLift_shift hΦ hlift k.1 k.2
    have h0 := hab 0
    simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at h0
    exact ⟨a, b, by simp only [s, h0]; exact Prod.ext (by simp) (by simp)⟩
  obtain ⟨a₁, b₁, h₁⟩ := hint (1, 0)
  obtain ⟨a₂, b₂, h₂⟩ := hint (0, 1)
  refine ⟨!![a₁, a₂; b₁, b₂], fun p m n => ?_⟩
  have hk : ((m, n) : ℤ × ℤ) = m • ((1, 0) : ℤ × ℤ) + n • ((0, 1) : ℤ × ℤ) := by
    ext <;> simp
  have hσ : s (m, n) = m • s (1, 0) + n • s (0, 1) := by
    change σ (m, n) = m • σ (1, 0) + n • σ (0, 1)
    rw [hk, map_add, map_zsmul, map_zsmul]
  have h := hs p (m, n)
  simp only at h
  rw [h, hσ, h₁, h₂]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem torusMatrix_eq_of_torusLift (hΦ : Continuous Φ)
    (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p)) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ (p : ℝ × ℝ) (m n : ℤ),
      Φ (p.1 + m, p.2 + n) =
        ((Φ p).1 + ((A 0 0 * m + A 0 1 * n : ℤ) : ℝ),
          (Φ p).2 + ((A 1 0 * m + A 1 1 * n : ℤ) : ℝ))) :
    torusMatrix φ = A := by
  let lin : ℝ × ℝ → ℝ × ℝ := fun p => (A 0 0 * p.1 + A 0 1 * p.2, A 1 0 * p.1 + A 1 1 * p.2)
  let G : unitInterval × (ℝ × ℝ) → Torus := fun q =>
    torusCover ((1 - (q.1 : ℝ)) * (Φ q.2).1 + q.1 * (lin q.2).1,
      (1 - (q.1 : ℝ)) * (Φ q.2).2 + q.1 * (lin q.2).2)
  have hGc : Continuous G := by
    refine continuous_torusCover.comp ?_
    have hl : Continuous lin := by fun_prop
    have ht : Continuous fun q : unitInterval × (ℝ × ℝ) => ((q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact (((continuous_const.sub ht).mul (hΦ.comp continuous_snd).fst).add
      (ht.mul (hl.comp continuous_snd).fst)).prodMk
      (((continuous_const.sub ht).mul (hΦ.comp continuous_snd).snd).add
      (ht.mul (hl.comp continuous_snd).snd))
  have hGper (t : unitInterval) (p : ℝ × ℝ) (m n : ℤ) :
      G (t, (p.1 + m, p.2 + n)) = G (t, p) := by
    simp only [G, lin, hA p m n]
    conv_rhs => rw [← torusCover_add_int _ (A 0 0 * m + A 0 1 * n) (A 1 0 * m + A 1 1 * n)]
    congr 1
    refine Prod.ext ?_ ?_ <;> simp only <;> push_cast <;> ring
  let H : unitInterval × Torus → Torus := fun q => G (q.1, torusSection q.2)
  have hHG : H ∘ Prod.map id torusCover = G := by
    funext q
    obtain ⟨m, n, hmn⟩ := exists_torusSection_torusCover q.2
    simp only [H, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, hmn]
    exact hGper q.1 q.2 m n
  have hHc : Continuous H := by
    have hq : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) torusCover) :=
      IsOpenQuotientMap.id.prodMap isOpenQuotientMap_torusCover
    rw [← hq.continuous_comp_iff, hHG]
    exact hGc
  have hF : torusAut ⟨φ, φ.continuous⟩ = torusAut (Circle.matrixContinuousMap A) :=
    torusAut_eq_of_homotopy
      { toFun := H
        continuous_toFun := hHc
        map_zero_left := fun z => by
          change G (0, torusSection z) = φ z
          simp only [G, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
          rw [Prod.mk.eta, ← hlift, torusCover_torusSection]
        map_one_left := fun z => by
          change G (1, torusSection z) = linearTorusMap A z
          simp only [G, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
          rw [← torusCover_torusSection z, linearTorusMap_torusCover, torusCover_torusSection] }
  rw [torusMatrix, torusMapMatrix, hF, ← torusMapMatrix, torusMapMatrix_matrixContinuousMap]

theorem torusLift_add_int (hΦ : Continuous Φ)
    (hlift : ∀ p, φ (torusCover p) = torusCover (Φ p)) (p : ℝ × ℝ) (m n : ℤ) :
    (Φ (p.1 + m, p.2 + n)).1 =
        (Φ p).1 + ((torusMatrix φ 0 0 * m + torusMatrix φ 0 1 * n : ℤ) : ℝ) ∧
      (Φ (p.1 + m, p.2 + n)).2 =
        (Φ p).2 + ((torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n : ℤ) : ℝ) := by
  obtain ⟨A, hA⟩ := exists_matrix_torusLift hΦ hlift
  rw [torusMatrix_eq_of_torusLift hΦ hlift A hA, hA p m n]
  exact ⟨rfl, rfl⟩

end Lift

theorem exists_torusLift (φ : TDiff) :
    ∃ Φ : ℝ × ℝ → ℝ × ℝ, ContDiff ℝ ∞ Φ ∧
      (∀ p, φ (torusCover p) = torusCover (Φ p)) ∧
      ∀ (p : ℝ × ℝ) (m n : ℤ),
        (Φ (p.1 + m, p.2 + n)).1 =
          (Φ p).1 + ((torusMatrix φ 0 0 * m + torusMatrix φ 0 1 * n : ℤ) : ℝ) ∧
        (Φ (p.1 + m, p.2 + n)).2 =
          (Φ p).2 + ((torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n : ℤ) : ℝ) := by
  have hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) torusModel ∞ (fun p => φ (torusCover p)) :=
    φ.contMDiff.comp contMDiff_torusCover
  obtain ⟨F₁, hF₁, h₁⟩ := exists_contDiff_cexp_lift (contMDiff_fst.comp hf)
  obtain ⟨F₂, hF₂, h₂⟩ := exists_contDiff_cexp_lift (contMDiff_snd.comp hf)
  have hlift (p : ℝ × ℝ) : φ (torusCover p) = torusCover (F₁ p, F₂ p) := by
    rw [torusCover_eq (F₁ p, F₂ p)]
    exact Prod.ext (h₁ p).symm (h₂ p).symm
  exact ⟨fun p => (F₁ p, F₂ p), hF₁.prodMk hF₂, hlift,
    torusLift_add_int (hF₁.prodMk hF₂).continuous hlift⟩

theorem eq_of_torusCover_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {F F' : A → ℝ × ℝ} (hF : Continuous F) (hF' : Continuous F')
    (h : ∀ a, torusCover (F' a) = torusCover (F a)) {a₀ : A} (h₀ : F' a₀ = F a₀) : F' = F := by
  obtain ⟨m, n, hmn⟩ := exists_int_of_torusCover_eq hF hF' h a₀
  have h₁ := hmn a₀
  rw [h₀] at h₁
  have hm : (m : ℝ) = 0 := by
    have := congrArg Prod.fst h₁
    simp only at this
    linarith
  have hn : (n : ℝ) = 0 := by
    have := congrArg Prod.snd h₁
    simp only at this
    linarith
  funext a
  rw [hmn a, hm, hn, add_zero, add_zero]

theorem exists_torusLift_apply_eq (φ : TDiff) {p₀ q₀ : ℝ × ℝ}
    (h₀ : φ (torusCover p₀) = torusCover q₀) :
    ∃ Φ : ℝ × ℝ → ℝ × ℝ, ContDiff ℝ ∞ Φ ∧ Φ p₀ = q₀ ∧
      ∀ p, φ (torusCover p) = torusCover (Φ p) := by
  obtain ⟨Φ, hΦ, hlift, -⟩ := exists_torusLift φ
  obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp ((hlift p₀).symm.trans h₀)
  refine ⟨fun p => ((Φ p).1 - m, (Φ p).2 - n),
    (hΦ.fst.sub contDiff_const).prodMk (hΦ.snd.sub contDiff_const), ?_, fun p => ?_⟩
  · simp only [hmn, add_sub_cancel_right]
  · rw [hlift, ← torusCover_add_int (((Φ p).1 - m, (Φ p).2 - n) : ℝ × ℝ) m n]
    simp only [sub_add_cancel]

theorem exists_torusLiftDiffeomorph (φ : TDiff) {p₀ q₀ : ℝ × ℝ}
    (h₀ : φ (torusCover p₀) = torusCover q₀) :
    ∃ Φ : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ), Φ p₀ = q₀ ∧
      (∀ p, φ (torusCover p) = torusCover (Φ p)) ∧
      (∀ p, φ.symm (torusCover p) = torusCover (Φ.symm p)) ∧
      ∀ (p : ℝ × ℝ) (m n : ℤ),
        (Φ (p.1 + m, p.2 + n)).1 =
          (Φ p).1 + ((torusMatrix φ 0 0 * m + torusMatrix φ 0 1 * n : ℤ) : ℝ) ∧
        (Φ (p.1 + m, p.2 + n)).2 =
          (Φ p).2 + ((torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n : ℤ) : ℝ) := by
  obtain ⟨Φ, hΦ, hΦ₀, hΦl⟩ := exists_torusLift_apply_eq φ h₀
  have h₀' : φ.symm (torusCover q₀) = torusCover p₀ := by
    rw [← h₀, Diffeomorph.symm_apply_apply]
  obtain ⟨Ψ, hΨ, hΨ₀, hΨl⟩ := exists_torusLift_apply_eq φ.symm h₀'
  have hΦΨ : (fun q => Φ (Ψ q)) = id :=
    eq_of_torusCover_eq continuous_id (hΦ.continuous.comp hΨ.continuous)
      (fun q => by rw [← hΦl, ← hΨl, Diffeomorph.apply_symm_apply, id])
      (a₀ := q₀) (by simp only [hΨ₀, hΦ₀, id])
  have hΨΦ : (fun p => Ψ (Φ p)) = id :=
    eq_of_torusCover_eq continuous_id (hΨ.continuous.comp hΦ.continuous)
      (fun p => by rw [← hΨl, ← hΦl, Diffeomorph.symm_apply_apply, id])
      (a₀ := p₀) (by simp only [hΨ₀, hΦ₀, id])
  let D : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ (ℝ × ℝ) :=
    { toFun := Φ
      invFun := Ψ
      left_inv := fun p => congrFun hΨΦ p
      right_inv := fun q => congrFun hΦΨ q
      contMDiff_toFun := hΦ.contMDiff
      contMDiff_invFun := hΨ.contMDiff }
  exact ⟨D, hΦ₀, hΦl, hΨl, torusLift_add_int hΦ.continuous hΦl⟩

def timeCover (q : ℝ × (ℝ × ℝ)) : ℝ × Torus := (q.1, torusCover q.2)

theorem isLocalDiffeomorph_timeCover :
    IsLocalDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ).prod torusModel) ∞ timeCover :=
  (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).isLocalDiffeomorph.prodMap isLocalDiffeomorph_torusCover

theorem timeCover_surjective : Function.Surjective timeCover := by
  rintro ⟨t, z⟩
  obtain ⟨p, rfl⟩ := torusCover_surjective z
  exact ⟨(t, p), rfl⟩

theorem contMDiff_of_contDiff_timeCover {G : ℝ × (ℝ × ℝ) → ℝ × ℝ} (hG : ContDiff ℝ ∞ G)
    {f : ℝ × Torus → Torus} (hf : ∀ q, f (timeCover q) = torusCover (G q)) :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞ f := by
  refine isLocalDiffeomorph_timeCover.contMDiff_of_comp_of_surjective timeCover_surjective ?_
  have h : f ∘ timeCover = torusCover ∘ G := funext hf
  rw [h]
  exact contMDiff_torusCover.comp (hG.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd))

section Family

variable (G : ℝ × (ℝ × ℝ) → ℝ × ℝ)

def torusFamilyMap (t : ℝ) (z : Torus) : Torus := torusCover (G (t, torusSection z))

variable {G}

theorem torusFamilyMap_torusCover
    (hper : ∀ t p (m n : ℤ), torusCover (G (t, (p.1 + m, p.2 + n))) = torusCover (G (t, p)))
    (t : ℝ) (p : ℝ × ℝ) : torusFamilyMap G t (torusCover p) = torusCover (G (t, p)) := by
  obtain ⟨m, n, hmn⟩ := exists_torusSection_torusCover p
  rw [torusFamilyMap, hmn, hper]

theorem contMDiff_torusFamilyMap (hG : ContDiff ℝ ∞ G)
    (hper : ∀ t p (m n : ℤ), torusCover (G (t, (p.1 + m, p.2 + n))) = torusCover (G (t, p))) :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => torusFamilyMap G q.1 q.2) :=
  contMDiff_of_contDiff_timeCover hG fun q => torusFamilyMap_torusCover hper q.1 q.2

variable {Ginv : ℝ × (ℝ × ℝ) → ℝ × ℝ}

def torusFamily (hG : ContDiff ℝ ∞ G) (hGinv : ContDiff ℝ ∞ Ginv)
    (hleft : ∀ t p, Ginv (t, G (t, p)) = p) (hright : ∀ t p, G (t, Ginv (t, p)) = p)
    (hper : ∀ t p (m n : ℤ), torusCover (G (t, (p.1 + m, p.2 + n))) = torusCover (G (t, p)))
    (hperinv : ∀ t p (m n : ℤ),
      torusCover (Ginv (t, (p.1 + m, p.2 + n))) = torusCover (Ginv (t, p)))
    (t : ℝ) : TDiff where
  toFun := torusFamilyMap G t
  invFun := torusFamilyMap Ginv t
  left_inv z := by
    obtain ⟨p, rfl⟩ := torusCover_surjective z
    rw [torusFamilyMap_torusCover hper, torusFamilyMap_torusCover hperinv, hleft]
  right_inv z := by
    obtain ⟨p, rfl⟩ := torusCover_surjective z
    rw [torusFamilyMap_torusCover hperinv, torusFamilyMap_torusCover hper, hright]
  contMDiff_toFun :=
    (contMDiff_torusFamilyMap hG hper).comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun :=
    (contMDiff_torusFamilyMap hGinv hperinv).comp (contMDiff_const.prodMk contMDiff_id)

theorem isotopicDiffeomorph_of_lift {φ ψ : TDiff} (hG : ContDiff ℝ ∞ G)
    (hGinv : ContDiff ℝ ∞ Ginv)
    (hleft : ∀ t p, Ginv (t, G (t, p)) = p) (hright : ∀ t p, G (t, Ginv (t, p)) = p)
    (hper : ∀ t p (m n : ℤ), torusCover (G (t, (p.1 + m, p.2 + n))) = torusCover (G (t, p)))
    (hperinv : ∀ t p (m n : ℤ),
      torusCover (Ginv (t, (p.1 + m, p.2 + n))) = torusCover (Ginv (t, p)))
    (h₀ : ∀ p, φ (torusCover p) = torusCover (G (0, p)))
    (h₁ : ∀ p, ψ (torusCover p) = torusCover (G (1, p))) :
    IsotopicDiffeomorph φ ψ := by
  refine ⟨torusFamily hG hGinv hleft hright hper hperinv, contMDiff_torusFamilyMap hG hper,
    contMDiff_torusFamilyMap hGinv hperinv, ?_, ?_⟩
  · refine Diffeomorph.ext fun z => ?_
    obtain ⟨p, rfl⟩ := torusCover_surjective z
    exact (torusFamilyMap_torusCover hper 0 p).trans (h₀ p).symm
  · refine Diffeomorph.ext fun z => ?_
    obtain ⟨p, rfl⟩ := torusCover_surjective z
    exact (torusFamilyMap_torusCover hper 1 p).trans (h₁ p).symm

end Family

section EasyLayer

theorem pos_or_neg_of_forall_ne_zero {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (h : ∀ x, f x ≠ 0) : (∀ x, 0 < f x) ∨ ∀ x, f x < 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
  obtain ⟨c, -, hc⟩ := isPreconnected_univ.intermediate_value (mem_univ a) (mem_univ b)
    hf.continuousOn ⟨ha, hb⟩
  exact h c hc

theorem bijective_of_hasDerivAt_sign {f f' : ℝ → ℝ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 < (ε : ℝ) * f' x)
    (hper : ∀ x (n : ℤ), f (x + n) = f x + ε * n) : Function.Bijective f := by
  have hε2 : (ε : ℝ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hg : Function.Bijective (fun x => (ε : ℝ) * f x) := by
    refine bijective_of_deriv_pos_of_add_int (fun x => ?_) (fun x n => ?_)
    · rw [((hf x).const_mul (ε : ℝ)).deriv]
      exact hpos x
    · rw [hper, mul_add, ← mul_assoc, hε2, one_mul]
  have hmul : Function.Bijective (fun y : ℝ => (ε : ℝ) * y) := by
    refine ⟨fun y y' h => ?_, fun y => ⟨ε * y, by simp only [← mul_assoc, hε2, one_mul]⟩⟩
    have := congrArg (fun z => (ε : ℝ) * z) h
    simpa only [← mul_assoc, hε2, one_mul] using this
  have hcomp : f = (fun y : ℝ => (ε : ℝ) * y) ∘ (fun x => (ε : ℝ) * f x) := by
    funext x
    simp only [Function.comp, ← mul_assoc, hε2, one_mul]
  rw [hcomp]
  exact hmul.comp hg

theorem hasDerivAt_comp_prodMk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E × ℝ → ℝ} (hh : Differentiable ℝ h) (p : E) (x : ℝ) :
    HasDerivAt (fun y => h (p, y)) (fderiv ℝ h (p, x) (0, 1)) x :=
  (hh (p, x)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_const x p).prodMk (hasDerivAt_id x))

theorem exists_contDiff_inverse_of_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {h h' : E × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hd : ∀ p x, HasDerivAt (fun y => h (p, y)) (h' (p, x)) x)
    (hpos : ∀ p x, 0 < (ε : ℝ) * h' (p, x))
    (hper : ∀ p x (n : ℤ), h (p, x + n) = h (p, x) + ε * n) :
    ∃ R : E × ℝ → ℝ, ContDiff ℝ ∞ R ∧ (∀ p x, R (p, h (p, x)) = x) ∧
      ∀ p y, h (p, R (p, y)) = y := by
  obtain ⟨R, hR, h1, h2⟩ := DifferentialGeometry.Analysis.exists_contDiffOn_inverse_of_bijective
    (h := h) (V := univ) isOpen_univ hh.contDiffOn
    (fun p _ => bijective_of_hasDerivAt_sign hε (hd p) (fun x => hpos p x) (hper p))
    (fun p _ x => by
      rw [(hasDerivAt_comp_prodMk (hh.differentiable (by simp)) p x).unique (hd p x)]
      intro h0
      have := hpos p x
      rw [h0, mul_zero] at this
      exact lt_irrefl _ this)
  refine ⟨R, ?_, fun p x => h1 p (mem_univ p) x, fun p y => h2 p (mem_univ p) y⟩
  rw [← contDiffOn_univ]
  simpa only [univ_prod_univ] using hR

theorem pos_convex_add {s X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hX : 0 < X) :
    0 < (1 - s) * X + s := by
  rcases eq_or_lt_of_le hs1 with h | h
  · rw [h]
    norm_num
  · nlinarith [mul_pos (sub_pos.mpr h) hX]

theorem exists_fibrePreserving_lift (φ : TDiff)
    (hφ : ∀ u v v' : Circle, (φ (u, v)).1 = (φ (u, v')).1) :
    ∃ (a : ℝ → ℝ) (b : ℝ × ℝ → ℝ), ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      (∀ p, φ (torusCover p) = torusCover (a p.1, b p)) ∧
      torusMatrix φ 0 1 = 0 ∧
      (torusMatrix φ 0 0 = 1 ∨ torusMatrix φ 0 0 = -1) ∧
      (torusMatrix φ 1 1 = 1 ∨ torusMatrix φ 1 1 = -1) ∧
      (∀ x, 0 < (torusMatrix φ 0 0 : ℝ) * deriv a x) ∧
      (∀ x y, 0 < (torusMatrix φ 1 1 : ℝ) * deriv (fun y => b (x, y)) y) ∧
      (∀ x (m : ℤ), a (x + m) = a x + torusMatrix φ 0 0 * m) ∧
      ∀ (p : ℝ × ℝ) (m n : ℤ),
        b (p.1 + m, p.2 + n) = b p + (torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n) := by
  obtain ⟨Φ, -, hlift, -, hdeck⟩ := exists_torusLiftDiffeomorph φ (p₀ := 0)
    (torusCover_torusSection (φ (torusCover 0))).symm
  have hΦ : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ → ℝ, a = fun x => (Φ (x, 0)).1 := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ × ℝ → ℝ, b = fun p => (Φ p).2 := ⟨_, rfl⟩
  have ha : ContDiff ℝ ∞ a := by
    rw [ha_def]
    exact hΦ.fst.comp (contDiff_id.prodMk contDiff_const)
  have hb : ContDiff ℝ ∞ b := by
    rw [hb_def]
    exact hΦ.snd
  have hP (x y : ℝ) : (Φ (x, y)).1 = a x := by
    have hc : ∀ y', cexp (Φ (x, y')).1 = cexp (a x) := fun y' => by
      have h1 := congrArg Prod.fst (hlift (x, y'))
      have h2 := congrArg Prod.fst (hlift (x, 0))
      rw [torusCover_eq, torusCover_eq] at h1 h2
      dsimp only at h1 h2
      rw [ha_def, ← h1, hφ (cexp x) (cexp y') (cexp 0), h2]
    obtain ⟨n, hn⟩ := exists_int_of_cexp_eq (F := fun _ : ℝ => a x)
      (F' := fun y' => (Φ (x, y')).1) continuous_const
      (hΦ.continuous.fst.comp (continuous_const.prodMk continuous_id)) hc 0
    have h0 := hn 0
    have hn0 : (n : ℝ) = 0 := by
      rw [ha_def] at h0
      dsimp only at h0
      linarith
    rw [hn y, hn0, add_zero]
  have hb' (p : ℝ × ℝ) : (Φ p).2 = b p := by rw [hb_def]
  have hA01 : torusMatrix φ 0 1 = 0 := by
    have h := (hdeck (0, 0) 0 1).1
    simp only [Int.cast_zero, Int.cast_one, add_zero, zero_add, hP, mul_zero, mul_one,
      left_eq_add, Int.cast_eq_zero] at h
    exact h
  have hdet : torusMatrix φ 0 0 * torusMatrix φ 1 1 = 1 ∨
      torusMatrix φ 0 0 * torusMatrix φ 1 1 = -1 := by
    have h := torusMatrix_det φ
    rwa [Matrix.det_fin_two, hA01, zero_mul, sub_zero] at h
  have hunit : IsUnit (torusMatrix φ 0 0 * torusMatrix φ 1 1) := Int.isUnit_iff.mpr hdet
  have hA00 : torusMatrix φ 0 0 = 1 ∨ torusMatrix φ 0 0 = -1 :=
    Int.isUnit_iff.mp (isUnit_of_mul_isUnit_left hunit)
  have hA11 : torusMatrix φ 1 1 = 1 ∨ torusMatrix φ 1 1 = -1 :=
    Int.isUnit_iff.mp (isUnit_of_mul_isUnit_right hunit)
  have hpa (x : ℝ) (m : ℤ) : a (x + m) = a x + torusMatrix φ 0 0 * m := by
    have h := (hdeck (x, 0) m 0).1
    simp only [Int.cast_zero, add_zero, hP, mul_zero, hA01] at h
    rw [h]
    push_cast
    ring
  have hpb (p : ℝ × ℝ) (m n : ℤ) :
      b (p.1 + m, p.2 + n) = b p + (torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n) := by
    have h := (hdeck p m n).2
    rw [hb', hb'] at h
    rw [h]
    push_cast
    ring
  have hinj (q : ℝ × ℝ) : Function.Injective (fderiv ℝ Φ q) := by
    have hΨd : DifferentiableAt ℝ Φ.symm (Φ q) :=
      ((contMDiff_iff_contDiff.mp Φ.symm.contMDiff).differentiable (by simp)) _
    have hcomp : HasFDerivAt (Φ.symm ∘ Φ) ((fderiv ℝ Φ.symm (Φ q)).comp (fderiv ℝ Φ q)) q :=
      hΨd.hasFDerivAt.comp q (hΦd q).hasFDerivAt
    have hid : (Φ.symm ∘ Φ : ℝ × ℝ → ℝ × ℝ) = id := funext fun p => Φ.symm_apply_apply p
    rw [hid] at hcomp
    have hu := hcomp.unique (hasFDerivAt_id q)
    intro v w hvw
    have h1 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L v) hu
    have h2 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L w) hu
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, hvw]
  have hsecy (x y : ℝ) : HasDerivAt (fun y' => Φ (x, y')) (fderiv ℝ Φ (x, y) (0, 1)) y :=
    (hΦd (x, y)).hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  have hsecx (x y : ℝ) : HasDerivAt (fun x' => Φ (x', y)) (fderiv ℝ Φ (x, y) (1, 0)) x :=
    (hΦd (x, y)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  have h01 (x y : ℝ) : (fderiv ℝ Φ (x, y) (0, 1)).1 = 0 := by
    have h1 := hasFDerivAt_fst.comp_hasDerivAt y (hsecy x y)
    have h2 : (Prod.fst ∘ fun y' => Φ (x, y')) = fun _ => a x := funext fun y' => hP x y'
    rw [h2] at h1
    exact h1.unique (hasDerivAt_const y (a x))
  have h10 (x y : ℝ) : (fderiv ℝ Φ (x, y) (1, 0)).1 = deriv a x := by
    have h1 := hasFDerivAt_fst.comp_hasDerivAt x (hsecx x y)
    have h2 : (Prod.fst ∘ fun x' => Φ (x', y)) = a := funext fun x' => hP x' y
    rw [h2] at h1
    exact h1.unique ((ha.differentiable (by simp)) x).hasDerivAt
  have hsb (x y : ℝ) : deriv (fun y' => b (x, y')) y = (fderiv ℝ Φ (x, y) (0, 1)).2 := by
    have h1 := hasFDerivAt_snd.comp_hasDerivAt y (hsecy x y)
    have h2 : (Prod.snd ∘ fun y' => Φ (x, y')) = fun y' => b (x, y') :=
      funext fun y' => hb' (x, y')
    rw [h2] at h1
    exact h1.deriv
  have hne (x y : ℝ) : deriv (fun y' => b (x, y')) y ≠ 0 ∧ deriv a x ≠ 0 := by
    have hβ : (fderiv ℝ Φ (x, y) (0, 1)).2 ≠ 0 := by
      intro h0
      have h3 : fderiv ℝ Φ (x, y) (0, 1) = fderiv ℝ Φ (x, y) 0 := by
        rw [map_zero]
        exact Prod.ext (h01 x y) h0
      have h4 := hinj (x, y) h3
      simp at h4
    refine ⟨by rw [hsb]; exact hβ, fun h0 => hβ ?_⟩
    have hv : fderiv ℝ Φ (x, y) ((fderiv ℝ Φ (x, y) (0, 1)).2 • ((1 : ℝ), (0 : ℝ)) -
        (fderiv ℝ Φ (x, y) (1, 0)).2 • ((0 : ℝ), (1 : ℝ))) = fderiv ℝ Φ (x, y) 0 := by
      rw [map_sub, map_smul, map_smul, map_zero]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, h01, h10, h0, Prod.fst_zero]
        ring
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul, Prod.snd_zero]
        ring
    have h4 := congrArg Prod.fst (hinj (x, y) hv)
    simpa using h4
  have hda : Continuous (deriv a) := ha.continuous_deriv (by simp)
  have hdb : Continuous (fun p : ℝ × ℝ => deriv (fun y' => b (p.1, y')) p.2) := by
    have h : (fun p : ℝ × ℝ => deriv (fun y' => b (p.1, y')) p.2) =
        fun p => (fderiv ℝ Φ p (0, 1)).2 := funext fun p => hsb p.1 p.2
    rw [h]
    exact ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const).snd
  have hsa : ∀ x, 0 < (torusMatrix φ 0 0 : ℝ) * deriv a x := by
    have h1 := hpa 0 1
    simp only [Int.cast_one, zero_add, mul_one] at h1
    rcases pos_or_neg_of_forall_ne_zero hda (fun x => (hne x 0).2) with hpos | hneg
    · have h2 := strictMono_of_deriv_pos hpos (show (0 : ℝ) < 1 by norm_num)
      rw [h1] at h2
      have hA : torusMatrix φ 0 0 = 1 := by
        rcases hA00 with h | h
        · exact h
        · rw [h] at h2
          norm_num at h2
      intro x
      rw [hA, Int.cast_one, one_mul]
      exact hpos x
    · have h2 := strictAnti_of_deriv_neg hneg (show (0 : ℝ) < 1 by norm_num)
      rw [h1] at h2
      have hA : torusMatrix φ 0 0 = -1 := by
        rcases hA00 with h | h
        · rw [h] at h2
          norm_num at h2
        · exact h
      intro x
      rw [hA, Int.cast_neg, Int.cast_one, neg_one_mul, neg_pos]
      exact hneg x
  have hsb' : ∀ x y, 0 < (torusMatrix φ 1 1 : ℝ) * deriv (fun y => b (x, y)) y := by
    have h1 := hpb (0, 0) 0 1
    simp only [Int.cast_zero, Int.cast_one, add_zero, zero_add, mul_zero, mul_one] at h1
    rcases pos_or_neg_of_forall_ne_zero hdb (fun p => (hne p.1 p.2).1) with hpos | hneg
    · have h2 := strictMono_of_deriv_pos (f := fun y => b (0, y)) (fun y => hpos (0, y))
        (show (0 : ℝ) < 1 by norm_num)
      simp only at h2
      rw [h1] at h2
      have hA : torusMatrix φ 1 1 = 1 := by
        rcases hA11 with h | h
        · exact h
        · rw [h] at h2
          norm_num at h2
      intro x y
      rw [hA, Int.cast_one, one_mul]
      exact hpos (x, y)
    · have h2 := strictAnti_of_deriv_neg (f := fun y => b (0, y)) (fun y => hneg (0, y))
        (show (0 : ℝ) < 1 by norm_num)
      simp only at h2
      rw [h1] at h2
      have hA : torusMatrix φ 1 1 = -1 := by
        rcases hA11 with h | h
        · rw [h] at h2
          norm_num at h2
        · exact h
      intro x y
      rw [hA, Int.cast_neg, Int.cast_one, neg_one_mul, neg_pos]
      exact hneg (x, y)
  refine ⟨a, b, ha, hb, fun p => ?_, hA01, hA00, hA11, hsa, hsb', hpa, hpb⟩
  rw [hlift p, ← hb' p, ← hP p.1 p.2]

theorem isotopicDiffeomorph_linear_of_fst_eq (φ : TDiff)
    (hφ : ∀ u v v' : Circle, (φ (u, v)).1 = (φ (u, v')).1) :
    IsotopicDiffeomorph φ (linearTorusDiffeomorph (torusUnit φ)) := by
  obtain ⟨a, b, ha, hb, hlift, hA01, hA00, hA11, hsa, hsb, hpa, hpb⟩ :=
    exists_fibrePreserving_lift φ hφ
  have hτ : ContDiff ℝ ∞ (cutoff 0 1) := contDiff_cutoff 0 1
  have hτ0 : cutoff 0 1 0 = 0 := cutoff_of_le zero_lt_one le_rfl
  have hτ1 : cutoff 0 1 1 = 1 := cutoff_of_ge zero_lt_one le_rfl
  have hsq₁ : (torusMatrix φ 0 0 : ℝ) * torusMatrix φ 0 0 = 1 := by
    rcases hA00 with h | h <;> rw [h] <;> norm_num
  have hsq₂ : (torusMatrix φ 1 1 : ℝ) * torusMatrix φ 1 1 = 1 := by
    rcases hA11 with h | h <;> rw [h] <;> norm_num
  have hpb' (x y : ℝ) (n : ℤ) : b (x, y + n) = b (x, y) + torusMatrix φ 1 1 * n := by
    have h := hpb (x, y) 0 n
    simp only [Int.cast_zero, add_zero, mul_zero, zero_add] at h
    exact h
  obtain ⟨g₁, hg₁⟩ : ∃ g : ℝ × ℝ → ℝ,
      g = fun q => (1 - cutoff 0 1 q.1) * a q.2 + cutoff 0 1 q.1 * (torusMatrix φ 0 0 * q.2) :=
    ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g : (ℝ × ℝ) × ℝ → ℝ,
      g = fun q => (1 - cutoff 0 1 q.1.1) * b (q.1.2, q.2) +
        cutoff 0 1 q.1.1 * (torusMatrix φ 1 0 * q.1.2 + torusMatrix φ 1 1 * q.2) := ⟨_, rfl⟩
  have hg₁c : ContDiff ℝ ∞ g₁ := by
    rw [hg₁]
    exact ((contDiff_const.sub (hτ.comp contDiff_fst)).mul (ha.comp contDiff_snd)).add
      ((hτ.comp contDiff_fst).mul (contDiff_const.mul contDiff_snd))
  have hg₂c : ContDiff ℝ ∞ g₂ := by
    rw [hg₂]
    exact ((contDiff_const.sub (hτ.comp contDiff_fst.fst)).mul
      (hb.comp (contDiff_fst.snd.prodMk contDiff_snd))).add
      ((hτ.comp contDiff_fst.fst).mul ((contDiff_const.mul contDiff_fst.snd).add
        (contDiff_const.mul contDiff_snd)))
  have hd₁ (q : ℝ) (x : ℝ) : HasDerivAt (fun y => g₁ (q, y))
      ((1 - cutoff 0 1 q) * deriv a x + cutoff 0 1 q * torusMatrix φ 0 0) x := by
    rw [hg₁]
    have h := ((((ha.differentiable (by simp)) x).hasDerivAt).const_mul (1 - cutoff 0 1 q)).add
      (((hasDerivAt_id x).const_mul (torusMatrix φ 0 0 : ℝ)).const_mul (cutoff 0 1 q))
    exact h.congr_deriv (by simp)
  have hd₂ (q : ℝ × ℝ) (y : ℝ) : HasDerivAt (fun y => g₂ (q, y))
      ((1 - cutoff 0 1 q.1) * deriv (fun y => b (q.2, y)) y +
        cutoff 0 1 q.1 * torusMatrix φ 1 1) y := by
    rw [hg₂]
    have hby : HasDerivAt (fun y => b (q.2, y)) (deriv (fun y => b (q.2, y)) y) y :=
      ((hb.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y).hasDerivAt
    have h := (hby.const_mul (1 - cutoff 0 1 q.1)).add
      (((hasDerivAt_const y ((torusMatrix φ 1 0 : ℝ) * q.2)).add
        ((hasDerivAt_id y).const_mul (torusMatrix φ 1 1 : ℝ))).const_mul (cutoff 0 1 q.1))
    exact h.congr_deriv (by simp)
  have hpos₁ (q : ℝ) (x : ℝ) : 0 < (torusMatrix φ 0 0 : ℝ) *
      ((fun q : ℝ × ℝ => (1 - cutoff 0 1 q.1) * deriv a q.2 + cutoff 0 1 q.1 *
        torusMatrix φ 0 0) (q, x)) := by
    have h := pos_convex_add (cutoff_nonneg 0 1 q) (cutoff_le_one 0 1 q) (hsa x)
    have he : (torusMatrix φ 0 0 : ℝ) * ((1 - cutoff 0 1 q) * deriv a x +
        cutoff 0 1 q * torusMatrix φ 0 0) =
        (1 - cutoff 0 1 q) * ((torusMatrix φ 0 0 : ℝ) * deriv a x) +
          cutoff 0 1 q * ((torusMatrix φ 0 0 : ℝ) * torusMatrix φ 0 0) := by ring
    simp only
    rw [he, hsq₁, mul_one]
    exact h
  have hpos₂ (q : ℝ × ℝ) (y : ℝ) : 0 < (torusMatrix φ 1 1 : ℝ) *
      ((fun q : (ℝ × ℝ) × ℝ => (1 - cutoff 0 1 q.1.1) * deriv (fun y => b (q.1.2, y)) q.2 +
        cutoff 0 1 q.1.1 * torusMatrix φ 1 1) (q, y)) := by
    have h := pos_convex_add (cutoff_nonneg 0 1 q.1) (cutoff_le_one 0 1 q.1) (hsb q.2 y)
    have he : (torusMatrix φ 1 1 : ℝ) * ((1 - cutoff 0 1 q.1) * deriv (fun y => b (q.2, y)) y +
        cutoff 0 1 q.1 * torusMatrix φ 1 1) =
        (1 - cutoff 0 1 q.1) * ((torusMatrix φ 1 1 : ℝ) * deriv (fun y => b (q.2, y)) y) +
          cutoff 0 1 q.1 * ((torusMatrix φ 1 1 : ℝ) * torusMatrix φ 1 1) := by ring
    simp only
    rw [he, hsq₂, mul_one]
    exact h
  have hper₁ (q : ℝ) (x : ℝ) (n : ℤ) : g₁ (q, x + n) = g₁ (q, x) + torusMatrix φ 0 0 * n := by
    rw [hg₁]
    simp only
    rw [hpa]
    ring
  have hper₂ (q : ℝ × ℝ) (y : ℝ) (n : ℤ) :
      g₂ (q, y + n) = g₂ (q, y) + torusMatrix φ 1 1 * n := by
    rw [hg₂]
    simp only
    rw [hpb']
    ring
  have hshift₂ (t x y : ℝ) (m n : ℤ) : g₂ ((t, x + m), y + n) =
      g₂ ((t, x), y) + ((torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n : ℤ) : ℝ) := by
    rw [hg₂]
    simp only
    rw [show ((x + m, y + n) : ℝ × ℝ) = ((x, y).1 + m, (x, y).2 + n) from rfl, hpb]
    push_cast
    ring
  obtain ⟨R₁, hR₁, hR₁l, hR₁r⟩ := exists_contDiff_inverse_of_sign (E := ℝ)
    (h' := fun q : ℝ × ℝ => (1 - cutoff 0 1 q.1) * deriv a q.2 + cutoff 0 1 q.1 *
      torusMatrix φ 0 0) hg₁c hA00 (fun q x => hd₁ q x) hpos₁ hper₁
  obtain ⟨R₂, hR₂, hR₂l, hR₂r⟩ := exists_contDiff_inverse_of_sign (E := ℝ × ℝ)
    (h' := fun q : (ℝ × ℝ) × ℝ => (1 - cutoff 0 1 q.1.1) * deriv (fun y => b (q.1.2, y)) q.2 +
      cutoff 0 1 q.1.1 * torusMatrix φ 1 1) hg₂c hA11 (fun q y => hd₂ q y) hpos₂ hper₂
  let G : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun q => (g₁ (q.1, q.2.1), g₂ ((q.1, q.2.1), q.2.2))
  let Ginv : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun q =>
    (R₁ (q.1, q.2.1), R₂ ((q.1, R₁ (q.1, q.2.1)), q.2.2))
  have hG : ContDiff ℝ ∞ G :=
    (hg₁c.comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk
      (hg₂c.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))
  have hR₁' : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => R₁ (q.1, q.2.1)) :=
    hR₁.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hGinv : ContDiff ℝ ∞ Ginv :=
    hR₁'.prodMk (hR₂.comp ((contDiff_fst.prodMk hR₁').prodMk contDiff_snd.snd))
  have hleft (t : ℝ) (p : ℝ × ℝ) : Ginv (t, G (t, p)) = p := by
    simp only [G, Ginv, hR₁l, hR₂l]
  have hright (t : ℝ) (p : ℝ × ℝ) : G (t, Ginv (t, p)) = p := by
    simp only [G, Ginv, hR₁r, hR₂r]
  have hGshift (t : ℝ) (p : ℝ × ℝ) (m n : ℤ) : G (t, (p.1 + m, p.2 + n)) =
      ((G (t, p)).1 + ((torusMatrix φ 0 0 * m : ℤ) : ℝ),
        (G (t, p)).2 + ((torusMatrix φ 1 0 * m + torusMatrix φ 1 1 * n : ℤ) : ℝ)) := by
    simp only [G]
    rw [hper₁, hshift₂]
    push_cast
    rfl
  have hper (t : ℝ) (p : ℝ × ℝ) (m n : ℤ) :
      torusCover (G (t, (p.1 + m, p.2 + n))) = torusCover (G (t, p)) := by
    rw [hGshift, torusCover_add_int]
  have hGinj (t : ℝ) {u u' : ℝ × ℝ} (h : G (t, u) = G (t, u')) : u = u' := by
    rw [← hleft t u, h, hleft]
  have hperinv (t : ℝ) (p : ℝ × ℝ) (m n : ℤ) :
      torusCover (Ginv (t, (p.1 + m, p.2 + n))) = torusCover (Ginv (t, p)) := by
    have h : Ginv (t, (p.1 + m, p.2 + n)) =
        ((Ginv (t, p)).1 + ((torusMatrix φ 0 0 * m : ℤ) : ℝ),
          (Ginv (t, p)).2 + ((torusMatrix φ 1 1 *
            (n - torusMatrix φ 1 0 * (torusMatrix φ 0 0 * m)) : ℤ) : ℝ)) := by
      refine hGinj t ?_
      rw [hright, hGshift, hright]
      refine Prod.ext ?_ ?_
      · simp only
        push_cast
        linear_combination (-(m : ℝ)) * hsq₁
      · simp only
        push_cast
        linear_combination (-((n : ℝ) - (torusMatrix φ 1 0 : ℝ) *
          ((torusMatrix φ 0 0 : ℝ) * m))) * hsq₂
    rw [h, torusCover_add_int]
  refine isotopicDiffeomorph_of_lift hG hGinv hleft hright hper hperinv (fun p => ?_)
    (fun p => ?_)
  · rw [hlift]
    simp only [G, hg₁, hg₂, hτ0, sub_zero, one_mul, zero_mul, add_zero]
  · change linearTorusMap (torusMatrix φ) (torusCover p) = _
    rw [linearTorusMap_torusCover]
    simp only [G, hg₁, hg₂, hτ1, sub_self, zero_mul, one_mul, zero_add, hA01, Int.cast_zero,
      add_zero]

end EasyLayer

end GC.Seifert
