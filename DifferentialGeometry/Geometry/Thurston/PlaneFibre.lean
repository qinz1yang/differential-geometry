import DifferentialGeometry.Geometry.Thurston.FlatTorusRaw
import DifferentialGeometry.Geometry.Thurston.PlaneLattice

/-!
# Actual torus fibres of primitive affine deck coordinates

The actual coordinate plane and its constructed translation lattice descend through the
original Euclidean cover. Primitive integer increments identify its entire embedded quotient
with the actual circle level set. The ambient cover and pointwise circle equation are retained;
no torus fibre, raw presentation or metric-model identification is supplied.
-/

set_option autoImplicit false

noncomputable section

open Set Module Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff BigOperators

namespace GC.GraphManifold.FlatTorus

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "A1" => AddCircle (1 : ℝ)

private def planePeriod {V : Type*} [instV : NormedAddCommGroup V]
    [instSpace : NormedSpace ℝ V] (c : Basis (Fin 2) ℝ V) (x : V) : Torus :=
  (AddCircle.diffeomorphCircle (c.repr x 0 : A1),
    AddCircle.diffeomorphCircle (c.repr x 1 : A1))

private theorem planePeriod_local {V : Type*} [instV : NormedAddCommGroup V]
    [instSpace : NormedSpace ℝ V] [instFD : FiniteDimensional ℝ V]
    (c : Basis (Fin 2) ℝ V) :
    IsLocalDiffeomorph 𝓘(ℝ, V) torusModel ∞ (planePeriod c) := by
  let e := c.equivFun.toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hf : ContMDiff 𝓘(ℝ, V) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ e :=
    (c.coord 0).toContinuousLinearMap.contDiff.contMDiff.prodMk
      (c.coord 1).toContinuousLinearMap.contDiff.contMDiff
  have hi (y : ℝ × ℝ) : e.symm y = y.1 • c 0 + y.2 • c 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, Basis.equivFun_apply, c.repr_self]
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ∞ e.symm :=
    ((contMDiff_fst.smul contMDiff_const).add
      (contMDiff_snd.smul contMDiff_const)).congr hi
  let d : V ≃ₘ⟮𝓘(ℝ, V), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (ℝ × ℝ) :=
    { toEquiv := e.toEquiv, contMDiff_toFun := hf, contMDiff_invFun := hg }
  have hd := d.isLocalDiffeomorph
  have hq : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞
      (fun t : ℝ => AddCircle.diffeomorphCircle (t : A1)) := by
    intro t
    exact (AddCircle.isLocalDiffeomorph_coe t).comp (𝓡 1) Circle
      (AddCircle.diffeomorphCircle.isLocalDiffeomorph (t : A1))
  have hp := hq.prodMap hq
  intro x
  exact (hd x).comp torusModel Torus (hp (d x))

private theorem planePeriod_surjective {V : Type*} [instV : NormedAddCommGroup V]
    [instSpace : NormedSpace ℝ V] (c : Basis (Fin 2) ℝ V) : Surjective (planePeriod c) := by
  rintro ⟨t, u⟩
  obtain ⟨a, rfl⟩ := AddCircle.diffeomorphCircle.surjective t
  obtain ⟨b, rfl⟩ := AddCircle.diffeomorphCircle.surjective u
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
  exact ⟨x • c 0 + y • c 1, by simp [planePeriod, c.repr_self]⟩

private theorem planePeriod_eq_iff {V : Type*} [instV : NormedAddCommGroup V]
    [instSpace : NormedSpace ℝ V] {c : Basis (Fin 2) ℝ V} {x y : V} :
    planePeriod c x = planePeriod c y ↔ y - x ∈ Submodule.span ℤ (range c) := by
  have hcoe (a b : ℝ) : (a : A1) = (b : A1) ↔ ∃ m : ℤ, (m : ℝ) = b - a := by
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
    simp only [zsmul_eq_mul, mul_one, neg_add_eq_sub]
  have hcoords : planePeriod c x = planePeriod c y ↔
      ∀ j : Fin 2, (c.repr x j : A1) = (c.repr y j : A1) := by
    constructor
    · intro he j
      fin_cases j
      · exact AddCircle.diffeomorphCircle.injective (congrArg Prod.fst he)
      · exact AddCircle.diffeomorphCircle.injective (congrArg Prod.snd he)
    · intro he
      exact Prod.ext (congrArg AddCircle.diffeomorphCircle (he 0))
        (congrArg AddCircle.diffeomorphCircle (he 1))
  rw [hcoords, c.mem_span_iff_repr_mem ℤ]
  simp only [map_sub, Finsupp.sub_apply, Set.mem_range, algebraMap_int_eq, Int.coe_castRingHom]
  exact forall_congr' (fun j => hcoe _ _)

theorem exists_torusFibre_of_primitiveDeckCoordinate
    (Q : ConnectedClosedOrientedManifold 3) (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    (p : E3 → Q.Carrier) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (hs : Surjective p) (hrel : ∀ x y, p x = p y ↔ ∃ γ : G, γ.val x = y)
    (ell : E3 →L[ℝ] ℝ) (hel : Surjective ell)
    (hlin : ∀ γ : G, ∀ v, ell (γ.val.linearIsometryEquiv v) = ell v)
    (hint : ∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m)
    (hprimitive : ∀ m : ℤ, ∃ γ : G, ell (γ.val 0) = m)
    (hkernel : ∀ γ : G, ell (γ.val 0) = 0 → ∀ x, γ.val x = x + γ.val 0)
    (c : Basis (Fin 2) ℝ ell.toLinearMap.ker)
    (hc : Submodule.span ℤ (range c) = ZLattice.comap ℝ
      (Geometry.FlatSurface.affineTranslationModule G) ell.toLinearMap.ker.subtype) :
    ∃ (F : Q.Carrier → Circle) (f : Torus → Q.Carrier),
      ContMDiff (𝓡 3) (𝓡 1) ∞ F ∧ (∀ z, Surjective (mfderiv (𝓡 3) (𝓡 1) F z)) ∧
      IsSmoothEmbedding torusModel (𝓡 3) ∞ f ∧ range f = F ⁻¹' {1} ∧
      ∀ x, F (p x) = AddCircle.diffeomorphCircle (ell x : A1) := by
  let K := ell.toLinearMap.ker
  let q := planePeriod c
  have hq := planePeriod_local c
  have hqs := planePeriod_surjective c
  have hcoord (γ : G) (x : E3) : ell (γ.val x) = ell x + ell (γ.val 0) := by
    rw [Geometry.FlatSurface.affineIsometry_apply, map_add, hlin]
  have hr (v w : K) : p v.val = p w.val ↔ q v = q w := by
    rw [planePeriod_eq_iff, hc]
    change p v.val = p w.val ↔ (w.val - v.val) ∈
      Geometry.FlatSurface.affineTranslationModule G
    constructor
    · intro hvw
      obtain ⟨γ, hγ⟩ := (hrel _ _).mp hvw
      have hz : ell (γ.val 0) = 0 := by
        have he := congrArg ell hγ
        rw [hcoord] at he
        have hv : ell v.val = 0 := v.property
        have hw : ell w.val = 0 := w.property
        simpa [hv, hw] using he
      have he := hkernel γ hz v.val
      rw [hγ] at he
      have hd : w.val - v.val = γ.val 0 := by rw [he]; abel
      rw [hd]
      change AffineIsometryEquiv.constVAdd ℝ E3 (γ.val 0) ∈ G
      have hmap : AffineIsometryEquiv.constVAdd ℝ E3 (γ.val 0) = γ.val := by
        apply AffineIsometryEquiv.ext
        intro x
        simpa [vadd_eq_add, add_comm] using (hkernel γ hz x).symm
      rw [hmap]
      exact γ.property
    · intro hvw
      apply (hrel _ _).mpr
      refine ⟨⟨AffineIsometryEquiv.constVAdd ℝ E3 (w.val - v.val), hvw⟩, ?_⟩
      change (w.val - v.val) + v.val = w.val
      abel
  let r : K → Q.Carrier := fun v => p v.val
  let f : Torus → Q.Carrier := r ∘ surjInv hqs
  have hfq (v : K) : f (q v) = r v :=
    (hr _ _).mpr (surjInv_eq hqs (q v))
  have hi : ContMDiff 𝓘(ℝ, K) (𝓡 3) ∞ (fun v : K => (v : E3)) :=
    K.subtypeL.contDiff.contMDiff
  have hsm : ContMDiff torusModel (𝓡 3) ∞ f := by
    apply hq.contMDiff_of_comp_of_surjective hqs
    have he : f ∘ q = r := funext hfq
    rw [he]
    exact hp.contMDiff.comp hi
  have hinj : Injective f := by
    intro a b hab
    exact (surjInv_eq hqs a).symm.trans (((hr _ _).mp hab).trans (surjInv_eq hqs b))
  have hd (a : Torus) : Injective (mfderiv torusModel (𝓡 3) f a) := by
    obtain ⟨v, rfl⟩ := hqs a
    have he : f ∘ q = p ∘ (fun v : K => (v : E3)) := funext hfq
    have hdi : Injective (mfderiv 𝓘(ℝ, K) (𝓡 3)
        (fun w : K => (w : E3)) v) := by
      have hj : Injective (fderiv ℝ (fun w : K => (w : E3)) v) := by
        change Injective (fderiv ℝ (K.subtypeL : K → E3) v)
        rw [K.subtypeL.hasFDerivAt.fderiv]
        exact Subtype.val_injective
      rw [mfderiv_eq_fderiv]
      exact ((NormedSpace.fromTangentSpace v.val).symm.injective.comp hj).comp
        (NormedSpace.fromTangentSpace v).injective
    have hpdi : Injective (mfderiv 𝓘(ℝ, K) (𝓡 3)
        (p ∘ (fun w : K => (w : E3))) v) := by
      rw [mfderiv_comp v (hp.contMDiff.mdifferentiableAt (by simp))
        (hi.mdifferentiableAt (by simp))]
      exact ((hp v.val).mfderivToContinuousLinearEquiv (by simp)).injective.comp hdi
    have hdf : Injective (mfderiv 𝓘(ℝ, K) (𝓡 3) (f ∘ q) v) := he.symm ▸ hpdi
    rw [mfderiv_comp v (hsm.mdifferentiableAt (by simp))
      (hq.contMDiff.mdifferentiableAt (by simp))] at hdf
    have hdf' : Injective ((mfderiv torusModel (𝓡 3) f (q v)) ∘
        (mfderiv 𝓘(ℝ, K) torusModel q v)) := hdf
    exact hdf'.of_comp_right ((hq v).mfderivToContinuousLinearEquiv (by simp)).surjective
  have hemb : IsSmoothEmbedding torusModel (𝓡 3) ∞ f :=
    ⟨Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hsm hd,
      (hsm.continuous.isClosedEmbedding hinj).isEmbedding⟩
  obtain ⟨F, hF, hFs, hFd, hFp⟩ :=
    exists_circleSubmersion_of_affineDeckCoordinate (NoCuts.carrier Q) G p hp hs hrel
      ell hel hlin hint
  refine ⟨F, f, hF, hFd, hemb, ?_, hFp⟩
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨v, rfl⟩ := hqs t
    rw [hfq]
    change F (p v.val) = 1
    rw [hFp]
    have hv : ell v.val = 0 := v.property
    rw [hv]
    change AddCircle.homeomorphCircle one_ne_zero (0 : A1) = 1
    simp [AddCircle.homeomorphCircle_apply]
  · intro hz
    obtain ⟨x, rfl⟩ := hs z
    have hx : (ell x : A1) = 0 := by
      apply AddCircle.diffeomorphCircle.injective
      have hzero : AddCircle.diffeomorphCircle (0 : A1) = 1 := by
        change AddCircle.homeomorphCircle one_ne_zero (0 : A1) = 1
        simp [AddCircle.homeomorphCircle_apply]
      exact (hFp x).symm.trans (hz.trans hzero.symm)
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx
    have hm' : ell x = m := by simpa only [zsmul_eq_mul, mul_one] using hm.symm
    obtain ⟨γ, hγ⟩ := hprimitive m
    let y := γ.val.symm x
    have hy : γ.val y = x := γ.val.apply_symm_apply x
    have hy0 : ell y = 0 := by
      have he := congrArg ell hy
      rw [hcoord, hγ, hm'] at he
      linarith
    let v : K := ⟨y, hy0⟩
    refine ⟨q v, ?_⟩
    rw [hfq]
    exact (hrel _ _).mpr ⟨γ, hy⟩

end GC.GraphManifold.FlatTorus
