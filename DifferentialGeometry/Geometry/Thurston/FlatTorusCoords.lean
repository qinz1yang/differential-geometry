import DifferentialGeometry.Topology.Manifold.FibreDiffeo
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing

/-!
# Actual torus coordinates of a three-dimensional translation-periodic cover

A smooth onto local diffeomorphism whose actual fibres are the periods of a full real basis
has the smooth type of three circles. The pointwise coordinate equation uses the same basis
and original covering map. The basis need not be orthogonal; no metric comparison is claimed.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold.FlatTorus

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "A1" => AddCircle (1 : ℝ)
abbrev addTripleModel := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)
local notation "AM" => addTripleModel

def tripleLinear : (Fin 3 → ℝ) ≃ₗ[ℝ] (ℝ × ℝ) × ℝ where
  toFun x := ((x 0, x 1), x 2)
  invFun y := ![y.1.1, y.1.2, y.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv y := by rcases y with ⟨⟨a, b⟩, c⟩; rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def basisTriple (b : Module.Basis (Fin 3) ℝ E3) : E3 ≃L[ℝ] (ℝ × ℝ) × ℝ :=
  (b.equivFun.trans tripleLinear).toContinuousLinearEquiv

def periodicTriple (b : Module.Basis (Fin 3) ℝ E3) (x : E3) : (A1 × A1) × A1 :=
  ((((b.repr x 0 : ℝ) : A1), ((b.repr x 1 : ℝ) : A1)), ((b.repr x 2 : ℝ) : A1))

theorem periodicTriple_isLocalDiffeomorph (b : Module.Basis (Fin 3) ℝ E3) :
    IsLocalDiffeomorph (𝓡 3) AM ∞ (periodicTriple b) := by
  have hlin : ContMDiff (𝓡 3) AM ∞ (basisTriple b) :=
    (((b.coord 0).toContinuousLinearMap.contDiff.contMDiff).prodMk
      (b.coord 1).toContinuousLinearMap.contDiff.contMDiff).prodMk
      (b.coord 2).toContinuousLinearMap.contDiff.contMDiff
  have hinv (y : (ℝ × ℝ) × ℝ) : (basisTriple b).symm y =
      y.1.1 • b 0 + y.1.2 • b 1 + y.2 • b 2 := by
    apply (basisTriple b).injective
    rw [(basisTriple b).apply_symm_apply]
    simp [basisTriple, tripleLinear, Module.Basis.equivFun_apply, Fin.ext_iff]
  have hlinv : ContMDiff AM (𝓡 3) ∞ (basisTriple b).symm := by
    have hc : ContMDiff AM (𝓡 3) ∞ (fun y : (ℝ × ℝ) × ℝ =>
        y.1.1 • b 0 + y.1.2 • b 1 + y.2 • b 2) :=
      (((contMDiff_fst.comp contMDiff_fst).smul contMDiff_const).add
        ((contMDiff_snd.comp contMDiff_fst).smul contMDiff_const)).add
        (contMDiff_snd.smul contMDiff_const)
    exact hc.congr hinv
  let d : E3 ≃ₘ⟮𝓡 3, AM⟯ ((ℝ × ℝ) × ℝ) :=
    { toEquiv := (basisTriple b).toEquiv
      contMDiff_toFun := hlin
      contMDiff_invFun := hlinv }
  have hl : IsLocalDiffeomorph (𝓡 3) AM ∞ (basisTriple b) := d.isLocalDiffeomorph
  have hq := (AddCircle.isLocalDiffeomorph_coe.prodMap
    AddCircle.isLocalDiffeomorph_coe).prodMap AddCircle.isLocalDiffeomorph_coe
  intro x
  exact (hl x).comp AM ((A1 × A1) × A1) (hq (basisTriple b x))

theorem periodicTriple_surjective (b : Module.Basis (Fin 3) ℝ E3) :
    Surjective (periodicTriple b) := by
  rintro ⟨⟨a, d⟩, c⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective d
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  refine ⟨(basisTriple b).symm ((x, y), z), ?_⟩
  have h := (basisTriple b).apply_symm_apply ((x, y), z)
  change (((b.repr _ 0 : A1), (b.repr _ 1 : A1)), (b.repr _ 2 : A1)) = _
  exact congrArg (fun q : (ℝ × ℝ) × ℝ => (((q.1.1 : A1), (q.1.2 : A1)), (q.2 : A1))) h

private theorem unit_period_iff {a d : ℝ} :
    (a : A1) = (d : A1) ↔ ∃ m : ℤ, d - a = m := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, mul_one]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by linarith⟩

theorem periodicTriple_eq_iff {b : Module.Basis (Fin 3) ℝ E3} {x y : E3} :
    periodicTriple b x = periodicTriple b y ↔
      ∃ m : Fin 3 → ℤ, y - x = ∑ i, m i • b i := by
  have hcoord : periodicTriple b x = periodicTriple b y ↔
      ∀ i : Fin 3, (b.repr x i : A1) = (b.repr y i : A1) := by
    constructor
    · intro h i
      fin_cases i
      · exact congrArg (fun q => q.1.1) h
      · exact congrArg (fun q => q.1.2) h
      · exact congrArg Prod.snd h
    · intro h
      exact Prod.ext (Prod.ext (h 0) (h 1)) (h 2)
  rw [hcoord]
  constructor
  · intro h
    choose m hm using fun i => (unit_period_iff (a := b.repr x i) (d := b.repr y i)).mp (h i)
    refine ⟨m, ?_⟩
    calc
      y - x = ∑ i, b.repr (y - x) i • b i := (b.sum_repr _).symm
      _ = ∑ i, m i • b i := by
        congr 1
        funext i
        have hi : b.repr (y - x) i = (m i : ℝ) := by
          simpa only [map_sub, Finsupp.sub_apply] using hm i
        rw [hi, Int.cast_smul_eq_zsmul]
  · rintro ⟨m, hm⟩ i
    apply (unit_period_iff (a := b.repr x i) (d := b.repr y i)).mpr
    refine ⟨m i, ?_⟩
    have hi := congrArg (fun v : E3 => b.repr v i) hm
    simpa only [map_sub, Finsupp.sub_apply, map_sum, map_zsmul, b.repr_self,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, zsmul_eq_mul,
      mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hi

def addTripleCircle : ((A1 × A1) × A1) ≃ₘ⟮AM, torusModel.prod (𝓡 1)⟯ (Torus × Circle) where
  toEquiv := (AddCircle.diffeomorphCircle.toEquiv.prodCongr
    AddCircle.diffeomorphCircle.toEquiv).prodCongr AddCircle.diffeomorphCircle.toEquiv
  contMDiff_toFun :=
    ((AddCircle.diffeomorphCircle.contMDiff.comp (contMDiff_fst.comp contMDiff_fst)).prodMk
      (AddCircle.diffeomorphCircle.contMDiff.comp (contMDiff_snd.comp contMDiff_fst))).prodMk
      (AddCircle.diffeomorphCircle.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    ((AddCircle.diffeomorphCircle.symm.contMDiff.comp (contMDiff_fst.comp contMDiff_fst)).prodMk
      (AddCircle.diffeomorphCircle.symm.contMDiff.comp (contMDiff_snd.comp contMDiff_fst))).prodMk
      (AddCircle.diffeomorphCircle.symm.contMDiff.comp contMDiff_snd)

theorem exists_diffeomorph_torus_of_periodicCover (W : CompactCarrier.{u})
    (b : Module.Basis (Fin 3) ℝ E3) (p : E3 → W.Carrier)
    (hp : IsLocalDiffeomorph (𝓡 3) W.model ∞ p) (hs : Surjective p)
    (hrel : ∀ x y, p x = p y ↔ ∃ m : Fin 3 → ℤ, y - x = ∑ i, m i • b i) :
    ∃ e : W.Carrier ≃ₘ⟮W.model, torusModel.prod (𝓡 1)⟯ (Torus × Circle),
      ∀ x, e (p x) =
        ((AddCircle.diffeomorphCircle (b.repr x 0 : A1),
          AddCircle.diffeomorphCircle (b.repr x 1 : A1)),
          AddCircle.diffeomorphCircle (b.repr x 2 : A1)) := by
  obtain ⟨e, he⟩ := DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_same_cover_fibres
    p (periodicTriple b) hp (periodicTriple_isLocalDiffeomorph b) hs
    (periodicTriple_surjective b) (fun x y =>
      (hrel x y).trans (periodicTriple_eq_iff (b := b) (x := x) (y := y)).symm)
  refine ⟨e.trans addTripleCircle, ?_⟩
  intro x
  change addTripleCircle (e (p x)) = _
  rw [he x]
  rfl

end GC.GraphManifold.FlatTorus
