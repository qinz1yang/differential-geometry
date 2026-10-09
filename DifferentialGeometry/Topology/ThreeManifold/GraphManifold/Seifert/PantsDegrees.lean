import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledGoodness

/-!
# Degrees on the pants and goodness of one-filling blocks

Chapter 6, packet K10c.

Torus maps. Paths in a topological group satisfy the interchange law, so π₁ of a pointwise
product of maps is the product of the translated π₁ maps (`fundamentalGroup_map_mul`). On the
torus, K02's `torusAut` is homotopy invariant (`torusAut_eq_of_homotopy'`), translations act
trivially, and hence `torusMapMatrix` is additive in pointwise products (`torusMapMatrix_mul`),
vanishes on constants and satisfies `torusMapMatrix_zpow`. The coordinate maps `torusFst`
(`(s, w) ↦ (s, 1)`) and `torusSwap` have matrices `!![1, 0; 0, 0]` and `!![0, 1; 1, 0]`.

Circle degree. `circleDegree u` is the `(0, 0)` entry of the matrix of `(s, w) ↦ (u s, 1)`, whose
matrix is `!![circleDegree u, 0; 0, 0]`. It is additive (`circleDegree_mul`, `circleDegree_inv`),
`1` on the identity, `0` on constants and invariant along a family `I × S¹ → S¹`
(`circleDegree_eq_of_family`).

Pants. For any `PlanarBase k`, read through its embedding onto the round model,
`boundaryRetraction j` (K10) has degree `1` on circle `j`. For a hole `j`, the retraction (the
conjugated angle about the hole centre) has degree `-1` on the outer circle (the family
`conj (3t - s c)`, `planarOuterFamily`) and `0` on another hole at distance `> 1`
(`d + s t / 2`, `planarHoleFamily`). The collars orient the outer circle counterclockwise and the
holes clockwise, which gives these signs. An angle map about the origin is not defined on the
pants (the origin lies in `planarModel 3`), and none is needed. For `k = 3`,
`pantsTransverse f` (the other hole's retraction if `f` is a hole, the quotient of the two hole
retractions if `f` is the outer circle) has degree `0` exactly on circle `f`
(`circleDegree_pantsTransverse`).

Theta maps. On a product-fibred piece, `solidTheta e = (fibre, 1)^e` and
`productTheta f p q = (r_f, 1)^{-q} · (fibre, 1)^p · (1, v_f)` (`r_f` the retraction, `v_f` the
transverse map). On port `a` their matrices are `!![0, e; 0, 0]` and
`!![-q deg(r_f ∘ ι_a), p; deg(v_f ∘ ι_a), 0]`. With `e = p M₁₁ - q M₀₁` (`M` the matrix of the
filling's matching, first column `±(p, q)`), K10b's seam condition holds. The determinant on a
free port is `-p deg(v_f ∘ ι_a) ≠ 0`, since `p > 0`. Hence `isGoodBlock_of_one_filling`: every
Seifert block over a pants base with one filling is good, whatever the filling, and
`isGoodBlock_of_fillingCount_le_one`: `FilledBlockGoodness` holds for at most one filling. Two
fillings (`D²(p₁, p₂)`) remain open.
-/

set_option autoImplicit false

noncomputable section
open Set Multiplicative
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate unitInterval

universe u

namespace GC.Seifert

section BasepointChange

theorem changeBasepoint_refl {X : Type*} [TopologicalSpace X] {x : X}
    (g : FundamentalGroup X x) : fundamentalGroupChangeBasepoint (Path.refl x) g = g := by
  rw [fundamentalGroupChangeBasepoint_apply]
  change ((Path.Homotopic.Quotient.mk (Path.refl x)).trans g).trans
    (Path.Homotopic.Quotient.mk (Path.refl x)).symm = g
  rw [← Path.Homotopic.Quotient.mk_symm, Path.refl_symm, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]

theorem changeBasepoint_trans {X : Type*} [TopologicalSpace X] {z m n : X} (β : Path z m)
    (γ : Path m n) (g : FundamentalGroup X n) :
    fundamentalGroupChangeBasepoint (β.trans γ) g =
      fundamentalGroupChangeBasepoint β (fundamentalGroupChangeBasepoint γ g) := by
  simp only [fundamentalGroupChangeBasepoint_apply]
  change ((Path.Homotopic.Quotient.mk (β.trans γ)).trans g).trans
      (Path.Homotopic.Quotient.mk (β.trans γ)).symm =
    ((Path.Homotopic.Quotient.mk β).trans (((Path.Homotopic.Quotient.mk γ).trans g).trans
      (Path.Homotopic.Quotient.mk γ).symm)).trans (Path.Homotopic.Quotient.mk β).symm
  rw [← Path.Homotopic.Quotient.mk_symm, Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_symm]
  simp only [Path.Homotopic.Quotient.trans_assoc]

end BasepointChange

section TopologicalGroup
variable {Y K : Type*} [TopologicalSpace Y] [TopologicalSpace K] [Group K]
  [IsTopologicalGroup K]

def mulRightMap (b : K) : C(K, K) := ⟨fun x => x * b, by fun_prop⟩

def mulLeftMap (a : K) : C(K, K) := ⟨fun x => a * x, by fun_prop⟩

theorem fundamentalGroup_map_mul (F G : C(Y, K)) (y : Y) (g : FundamentalGroup Y y) :
    FundamentalGroup.map (F * G) y g =
      @id (FundamentalGroup K (F y * G y))
          (FundamentalGroup.map (mulRightMap (G y)) (F y) (FundamentalGroup.map F y g)) *
        @id (FundamentalGroup K (F y * G y))
          (FundamentalGroup.map (mulLeftMap (F y)) (G y) (FundamentalGroup.map G y g)) := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
    let γF := γ.map F.continuous
    let γG := γ.map G.continuous
    have h1 : (γF.prod γG).Homotopic (((Path.refl (F y)).trans γF).prod
        (γG.trans (Path.refl (G y)))) :=
      ⟨Path.Homotopic.prodHomotopy (Path.Homotopy.reflTrans γF).symm
        (Path.Homotopy.transRefl γG).symm⟩
    have h2 := h1.map ⟨fun p : K × K => p.1 * p.2, continuous_mul⟩
    rw [← Path.trans_prod_eq_prod_trans, Path.map_trans] at h2
    change Path.Homotopic.Quotient.mk (γ.map (F * G).continuous) =
      Path.Homotopic.Quotient.mk ((γG.map (mulLeftMap (F y)).continuous).trans
        (γF.map (mulRightMap (G y)).continuous))
    exact Path.Homotopic.Quotient.eq.2 h2

end TopologicalGroup

section TorusMaps

theorem torusAut_eq_of_homotopy' {f g : C(Torus, Torus)} (H : f.Homotopy g) :
    torusAut f = torusAut g := by
  rw [torusAut_eq f (PathConnectedSpace.somePath torusBase (f torusBase)),
    torusAut_eq g ((PathConnectedSpace.somePath torusBase (f torusBase)).trans
      (H.evalAt torusBase))]
  ext a
  have h := congrArg (fun φ => φ a) (GC.Topology.homotopy_track f g H torusBase)
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h ⊢
  rw [← h, changeBasepoint_trans]

theorem torusMapMatrix_eq_of_homotopy {f g : C(Torus, Torus)} (H : f.Homotopy g) :
    torusMapMatrix f = torusMapMatrix g := by
  rw [torusMapMatrix, torusMapMatrix, torusAut_eq_of_homotopy' H]

def mulRightHomotopy (b : Torus) : (mulRightMap b).Homotopy (ContinuousMap.id Torus) where
  toFun p := p.2 * (PathConnectedSpace.somePath b 1) p.1
  continuous_toFun := by fun_prop
  map_zero_left x := by simp [mulRightMap]
  map_one_left x := by simp

def mulLeftHomotopy (a : Torus) : (mulLeftMap a).Homotopy (ContinuousMap.id Torus) where
  toFun p := (PathConnectedSpace.somePath a 1) p.1 * p.2
  continuous_toFun := by fun_prop
  map_zero_left x := by simp [mulLeftMap]
  map_one_left x := by simp

theorem torusAut_mul_apply (F G : C(Torus, Torus)) (a : FundamentalGroup Torus torusBase) :
    torusAut (F * G) a = torusAut F a * torusAut G a := by
  let β := PathConnectedSpace.somePath torusBase ((F * G) torusBase)
  have hF : torusAut F = torusAut ((mulRightMap (G torusBase)).comp F) := by
    rw [torusAut_comp, torusAut_eq_of_homotopy' (mulRightHomotopy _), torusAut_id,
      MonoidHom.id_comp]
  have hG : torusAut G = torusAut ((mulLeftMap (F torusBase)).comp G) := by
    rw [torusAut_comp, torusAut_eq_of_homotopy' (mulLeftHomotopy _), torusAut_id,
      MonoidHom.id_comp]
  rw [hF, hG, torusAut_eq (F * G) β, torusAut_eq ((mulRightMap _).comp F) β,
    torusAut_eq ((mulLeftMap _).comp G) β]
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    GC.Topology.fundamentalGroup_map_comp]
  rw [fundamentalGroup_map_mul, map_mul]
  rfl

theorem exists_toAdd_torusCoordinates (v : Fin 2 → ℤ) :
    ∃ g, toAdd (torusCoordinates g) = v :=
  ⟨torusCoordinates.symm (ofAdd v), by simp⟩

theorem torusMapMatrix_mul (F G : C(Torus, Torus)) :
    torusMapMatrix (F * G) = torusMapMatrix F + torusMapMatrix G := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨g, rfl⟩ := exists_toAdd_torusCoordinates v
  rw [Matrix.add_mulVec, torusMapMatrix_mulVec, torusMapMatrix_mulVec, torusMapMatrix_mulVec,
    torusAut_mul_apply, map_mul, toAdd_mul]

theorem fundamentalGroup_map_const {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (c : Z) (x : X) (g : FundamentalGroup X x) :
    FundamentalGroup.map (ContinuousMap.const X c) x g = 1 := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk (p.map continuous_const) = Path.Homotopic.Quotient.refl c
    rw [← Path.Homotopic.Quotient.mk_refl]
    congr 1

theorem torusMapMatrix_const (c : Torus) : torusMapMatrix (ContinuousMap.const Torus c) = 0 := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨g, rfl⟩ := exists_toAdd_torusCoordinates v
  rw [torusMapMatrix_mulVec, Matrix.zero_mulVec,
    torusAut_eq _ (PathConnectedSpace.somePath torusBase c)]
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, fundamentalGroup_map_const, map_one,
    toAdd_one]

theorem torusMapMatrix_one : torusMapMatrix (1 : C(Torus, Torus)) = 0 :=
  torusMapMatrix_const 1

theorem torusMapMatrix_inv (F : C(Torus, Torus)) :
    torusMapMatrix F⁻¹ = -torusMapMatrix F := by
  have h := torusMapMatrix_mul F F⁻¹
  rw [mul_inv_cancel, torusMapMatrix_one] at h
  rw [eq_neg_iff_add_eq_zero, add_comm, ← h]

theorem torusMapMatrix_zpow (F : C(Torus, Torus)) (n : ℤ) :
    torusMapMatrix (F ^ n) = n • torusMapMatrix F := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, torusMapMatrix_one, zero_smul]
  | succ n ih => rw [zpow_add_one, torusMapMatrix_mul, ih, add_smul, one_smul]
  | pred n ih => rw [zpow_sub_one, torusMapMatrix_mul, ih, torusMapMatrix_inv, sub_smul, one_smul,
      sub_eq_add_neg]

theorem toAdd_torusCoordinates (g : FundamentalGroup Torus torusBase) :
    toAdd (torusCoordinates g) =
      ![toAdd (fundamentalGroupCircleEquivInt (FundamentalGroup.map ContinuousMap.fst torusBase g)),
        toAdd (fundamentalGroupCircleEquivInt
          (FundamentalGroup.map ContinuousMap.snd torusBase g))] := by
  ext i
  fin_cases i <;> rfl

def torusFst : C(Torus, Torus) := ⟨fun x => (x.1, 1), by fun_prop⟩

def torusSwap : C(Torus, Torus) := ⟨fun x => (x.2, x.1), by fun_prop⟩

theorem torusMapMatrix_torusFst : torusMapMatrix torusFst = !![1, 0; 0, 0] := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨g, rfl⟩ := exists_toAdd_torusCoordinates v
  have hA : torusAut torusFst g = FundamentalGroup.map torusFst torusBase g := by
    rw [torusAut_eq torusFst (Path.refl torusBase)]
    exact changeBasepoint_refl _
  rw [torusMapMatrix_mulVec, hA]
  have h1 : FundamentalGroup.map ContinuousMap.fst torusBase
      (FundamentalGroup.map torusFst torusBase g) =
        FundamentalGroup.map ContinuousMap.fst torusBase g := by
    induction g using Path.Homotopic.Quotient.ind
    rfl
  have h2 : FundamentalGroup.map ContinuousMap.snd torusBase
      (FundamentalGroup.map torusFst torusBase g) = 1 := by
    refine Eq.trans ?_ (fundamentalGroup_map_const (1 : Circle) torusBase g)
    induction g using Path.Homotopic.Quotient.ind
    rfl
  have h2' : fundamentalGroupCircleEquivInt (FundamentalGroup.map ContinuousMap.snd torusBase
      (FundamentalGroup.map torusFst torusBase g)) = 1 := by
    rw [h2]
    exact map_one _
  rw [toAdd_torusCoordinates (FundamentalGroup.map torusFst torusBase g),
    toAdd_torusCoordinates g, h1, h2']
  ext i
  fin_cases i <;> simp

theorem torusMapMatrix_torusSwap : torusMapMatrix torusSwap = !![0, 1; 1, 0] := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨g, rfl⟩ := exists_toAdd_torusCoordinates v
  have hA : torusAut torusSwap g = FundamentalGroup.map torusSwap torusBase g := by
    rw [torusAut_eq torusSwap (Path.refl torusBase)]
    exact changeBasepoint_refl _
  rw [torusMapMatrix_mulVec, hA]
  have h1 : FundamentalGroup.map ContinuousMap.fst torusBase
      (FundamentalGroup.map torusSwap torusBase g) =
        FundamentalGroup.map ContinuousMap.snd torusBase g := by
    induction g using Path.Homotopic.Quotient.ind
    rfl
  have h2 : FundamentalGroup.map ContinuousMap.snd torusBase
      (FundamentalGroup.map torusSwap torusBase g) =
        FundamentalGroup.map ContinuousMap.fst torusBase g := by
    induction g using Path.Homotopic.Quotient.ind
    rfl
  rw [toAdd_torusCoordinates (FundamentalGroup.map torusSwap torusBase g),
    toAdd_torusCoordinates g, h1, h2]
  ext i
  fin_cases i <;> simp

end TorusMaps

section CircleDegree

def circleMapTorus (u : C(Circle, Circle)) : C(Torus, Torus) := ⟨fun x => (u x.1, 1), by fun_prop⟩

def circleDegree (u : C(Circle, Circle)) : ℤ := torusMapMatrix (circleMapTorus u) 0 0

theorem torusMapMatrix_circleMapTorus (u : C(Circle, Circle)) :
    torusMapMatrix (circleMapTorus u) = !![circleDegree u, 0; 0, 0] := by
  have h : circleMapTorus u = torusFst.comp ((circleMapTorus u).comp torusFst) := rfl
  have hm := congrArg torusMapMatrix h
  rw [torusMapMatrix_comp, torusMapMatrix_comp, torusMapMatrix_torusFst] at hm
  rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, circleDegree]

theorem circleMapTorus_mul (u v : C(Circle, Circle)) :
    circleMapTorus (u * v) = circleMapTorus u * circleMapTorus v := by
  ext x <;> simp [circleMapTorus]

theorem circleMapTorus_inv (u : C(Circle, Circle)) :
    circleMapTorus u⁻¹ = (circleMapTorus u)⁻¹ := by
  ext x <;> simp [circleMapTorus]

theorem circleDegree_mul (u v : C(Circle, Circle)) :
    circleDegree (u * v) = circleDegree u + circleDegree v := by
  rw [circleDegree, circleMapTorus_mul, torusMapMatrix_mul]
  rfl

theorem circleDegree_inv (u : C(Circle, Circle)) : circleDegree u⁻¹ = -circleDegree u := by
  rw [circleDegree, circleMapTorus_inv, torusMapMatrix_inv]
  rfl

theorem circleDegree_id : circleDegree (ContinuousMap.id Circle) = 1 := by
  have h : circleMapTorus (ContinuousMap.id Circle) = torusFst := rfl
  rw [circleDegree, h, torusMapMatrix_torusFst]
  rfl

theorem circleDegree_const (c : Circle) : circleDegree (ContinuousMap.const Circle c) = 0 := by
  have h : circleMapTorus (ContinuousMap.const Circle c) = ContinuousMap.const Torus (c, 1) := rfl
  rw [circleDegree, h, torusMapMatrix_const]
  rfl

theorem circleDegree_eq_of_family (H : C(I × Circle, Circle)) {u v : C(Circle, Circle)}
    (hu : ∀ t, H (0, t) = u t) (hv : ∀ t, H (1, t) = v t) : circleDegree u = circleDegree v := by
  let K : (circleMapTorus u).Homotopy (circleMapTorus v) :=
    { toFun := fun p => (H (p.1, p.2.1), 1)
      continuous_toFun := by fun_prop
      map_zero_left := fun x => by simp [circleMapTorus, hu]
      map_one_left := fun x => by simp [circleMapTorus, hv] }
  rw [circleDegree, circleDegree, torusMapMatrix_eq_of_homotopy K]

def circleNormalize {X : Type*} [TopologicalSpace X] (V : X → ℂ) (hV : Continuous V)
    (h0 : ∀ x, V x ≠ 0) : C(X, Circle) :=
  ⟨fun x => ⟨V x / (‖V x‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (h0 x))])⟩,
    Continuous.subtype_mk (hV.div (Complex.continuous_ofReal.comp hV.norm) fun x =>
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (h0 x))) _⟩

theorem coe_circleNormalize {X : Type*} [TopologicalSpace X] (V : X → ℂ) (hV : Continuous V)
    (h0 : ∀ x, V x ≠ 0) (x : X) :
    (circleNormalize V hV h0 x : ℂ) = V x / (‖V x‖ : ℂ) :=
  rfl

theorem circleNormalize_real_mul {z : ℂ} {a : ℝ} (ha : 0 < a) (hz : ‖z‖ = 1) :
    (a : ℂ) * z / (‖(a : ℂ) * z‖ : ℂ) = z := by
  rw [norm_mul, Complex.norm_real, hz, mul_one, Real.norm_of_nonneg ha.le,
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 ha.ne')]

end CircleDegree

section Pants

theorem norm_three_mul_sub_ne_zero {c : ℝ} (hc : |c| < 3) (s : I) (t : Circle) :
    conj (3 * (t : ℂ) - ((s : ℝ) * c : ℝ)) ≠ 0 := by
  rw [map_ne_zero]
  intro h
  have h1 := congrArg (fun z => ‖z‖) h
  have h2 := norm_sub_norm_le (3 * (t : ℂ)) (((s : ℝ) * c : ℝ) : ℂ)
  simp only [norm_zero] at h1
  rw [h1, norm_mul, Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg s.2.1] at h2
  have h3 : (s : ℝ) * |c| ≤ |c| := mul_le_of_le_one_left (abs_nonneg c) s.2.2
  norm_num at h2
  linarith

def planarOuterFamily (c : ℝ) (hc : |c| < 3) : C(I × Circle, Circle) :=
  circleNormalize (fun p : I × Circle => conj (3 * (p.2 : ℂ) - ((p.1 : ℝ) * c : ℝ)))
    (by fun_prop) fun p => norm_three_mul_sub_ne_zero hc p.1 p.2

theorem add_half_mul_ne_zero {d : ℝ} (hd : 1 < |d|) (s : I) (t : Circle) :
    (d : ℂ) + ((s : ℝ) / 2 : ℝ) * (t : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z => ‖z‖) h
  have h2 := norm_sub_norm_le (d : ℂ) (-(((s : ℝ) / 2 : ℝ) * (t : ℂ)))
  simp only [norm_zero, sub_neg_eq_add] at h1 h2
  rw [h1, norm_neg, norm_mul, Circle.norm_coe, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg s.2.1 zero_le_two)] at h2
  have h3 : (s : ℝ) / 2 ≤ 1 / 2 := by linarith [s.2.2]
  linarith

def planarHoleFamily (d : ℝ) (hd : 1 < |d|) : C(I × Circle, Circle) :=
  circleNormalize (fun p : I × Circle => (d : ℂ) + ((p.1 : ℝ) / 2 : ℝ) * (p.2 : ℂ))
    (by fun_prop) fun p => add_half_mul_ne_zero hd p.1 p.2

namespace PlanarBase

variable {k : ℕ}

theorem coe_boundaryRetraction_boundaryCircle (B : PlanarBase.{u} k) (hk : 2 ≤ k)
    (j j' : Fin k) (t : Circle) :
    (B.boundaryRetraction hk j (B.boundaryCircle j' t) : ℂ) =
      planarRetractionVector k j (planarCircleMap k j' t) /
        (‖planarRetractionVector k j (planarCircleMap k j' t)‖ : ℂ) := by
  change planarRetractionVector k j (B.embedding (B.collar j' (t, halfZero))) /
    (‖planarRetractionVector k j (B.embedding (B.collar j' (t, halfZero)))‖ : ℂ) = _
  rw [B.embedding_collar]

theorem circleDegree_retraction_self (B : PlanarBase.{u} k) (hk : 2 ≤ k) (j : Fin k) :
    circleDegree ((B.boundaryRetraction hk j).comp (B.boundaryCircle j)) = 1 := by
  have h : (B.boundaryRetraction hk j).comp (B.boundaryCircle j) = ContinuousMap.id Circle :=
    ContinuousMap.ext (B.boundaryRetraction_leftInverse hk j)
  rw [h, circleDegree_id]

theorem circleDegree_retraction_outer (B : PlanarBase.{u} k) (hk : 2 ≤ k) {j j₀ : Fin k}
    (hj : j.val ≠ 0) (hj₀ : j₀.val = 0) (hc : |planarCenter k j| < 3) :
    circleDegree ((B.boundaryRetraction hk j).comp (B.boundaryCircle j₀)) = -1 := by
  have hV : ∀ t : Circle, planarRetractionVector k j (planarCircleMap k j₀ t) =
      conj (3 * (t : ℂ) - (((1 : I) : ℝ) * planarCenter k j : ℝ)) := by
    intro t
    have hc0 : planarCenter k j₀ = 0 := by simp [planarCenter, hj₀]
    simp [planarRetractionVector, planarCircleMap, planarRadius, hj, hj₀, hc0]
  rw [← circleDegree_eq_of_family (planarOuterFamily _ hc) (u := (ContinuousMap.id Circle)⁻¹)
    (fun t => ?_) (fun t => ?_), circleDegree_inv, circleDegree_id]
  · apply Circle.coe_injective
    change conj (3 * (t : ℂ) - (((0 : I) : ℝ) * planarCenter k j : ℝ)) /
      (‖conj (3 * (t : ℂ) - (((0 : I) : ℝ) * planarCenter k j : ℝ))‖ : ℂ) = ((t⁻¹ : Circle) : ℂ)
    rw [Circle.coe_inv_eq_conj]
    simp only [Set.Icc.coe_zero, zero_mul, Complex.ofReal_zero, sub_zero, map_mul]
    rw [show (conj (3 : ℂ)) = ((3 : ℝ) : ℂ) by rw [map_ofNat]; norm_num]
    exact circleNormalize_real_mul (by norm_num) (by simp)
  · apply Circle.coe_injective
    rw [ContinuousMap.comp_apply, coe_boundaryRetraction_boundaryCircle, hV]
    rfl

theorem circleDegree_retraction_hole (B : PlanarBase.{u} k) (hk : 2 ≤ k) {j j' : Fin k}
    (hj : j.val ≠ 0) (hj' : j'.val ≠ 0) (hd : 1 < |planarCenter k j' - planarCenter k j|) :
    circleDegree ((B.boundaryRetraction hk j).comp (B.boundaryCircle j')) = 0 := by
  have hV : ∀ t : Circle, planarRetractionVector k j (planarCircleMap k j' t) =
      ((planarCenter k j' - planarCenter k j : ℝ) : ℂ) + (((1 : I) : ℝ) / 2 : ℝ) * (t : ℂ) := by
    intro t
    simp only [planarRetractionVector, planarCircleMap, planarRadius, hj, hj', ite_false,
      map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj, Set.Icc.coe_one]
    push_cast
    ring
  let c : Circle := planarHoleFamily _ hd (0, 1)
  rw [← circleDegree_eq_of_family (planarHoleFamily _ hd) (u := ContinuousMap.const Circle c)
    (fun t => ?_) (fun t => ?_), circleDegree_const]
  · apply Circle.coe_injective
    simp only [c, ContinuousMap.const_apply, coe_circleNormalize, planarHoleFamily,
      Set.Icc.coe_zero, zero_div, Complex.ofReal_zero, zero_mul, add_zero]
  · apply Circle.coe_injective
    rw [ContinuousMap.comp_apply, coe_boundaryRetraction_boundaryCircle, hV]
    rfl

def pantsRetraction (B : PlanarBase.{u} k) (hk : k = 3) (i : ℕ) (hi : i < 3) :
    C(B.surface.Carrier, Circle) :=
  B.boundaryRetraction (by omega) ⟨i, by omega⟩

def pantsTransverse (B : PlanarBase.{u} k) (hk : k = 3) (f : Fin k) :
    C(B.surface.Carrier, Circle) :=
  if f.val = 1 then B.pantsRetraction hk 2 (by norm_num)
  else if f.val = 2 then B.pantsRetraction hk 1 (by norm_num)
  else B.pantsRetraction hk 1 (by norm_num) * (B.pantsRetraction hk 2 (by norm_num))⁻¹

theorem circleDegree_pantsTransverse (B : PlanarBase.{u} k) (hk : k = 3) (f a : Fin k) :
    circleDegree ((B.pantsTransverse hk f).comp (B.boundaryCircle a)) = 0 ↔ a = f := by
  subst hk
  have h10 : circleDegree ((B.pantsRetraction rfl 1 (by norm_num)).comp (B.boundaryCircle 0)) =
      -1 := B.circleDegree_retraction_outer _ (by decide) rfl (by norm_num [planarCenter])
  have h20 : circleDegree ((B.pantsRetraction rfl 2 (by norm_num)).comp (B.boundaryCircle 0)) =
      -1 := B.circleDegree_retraction_outer _ (by decide) rfl (by norm_num [planarCenter])
  have h11 : circleDegree ((B.pantsRetraction rfl 1 (by norm_num)).comp (B.boundaryCircle 1)) =
      1 := B.circleDegree_retraction_self _ _
  have h22 : circleDegree ((B.pantsRetraction rfl 2 (by norm_num)).comp (B.boundaryCircle 2)) =
      1 := B.circleDegree_retraction_self _ _
  have h12 : circleDegree ((B.pantsRetraction rfl 1 (by norm_num)).comp (B.boundaryCircle 2)) =
      0 := B.circleDegree_retraction_hole _ (by decide) (by decide) (by norm_num [planarCenter])
  have h21 : circleDegree ((B.pantsRetraction rfl 2 (by norm_num)).comp (B.boundaryCircle 1)) =
      0 := B.circleDegree_retraction_hole _ (by decide) (by decide) (by norm_num [planarCenter])
  fin_cases f <;> fin_cases a <;>
    simp [pantsTransverse, ContinuousMap.mul_comp, ContinuousMap.inv_comp, circleDegree_mul,
      circleDegree_inv, h10, h20, h11, h22, h12, h21]

end PlanarBase

end Pants

section Theta

theorem torusMapMatrix_fiberDirection :
    torusMapMatrix (torusFst.comp torusSwap) = !![0, 1; 0, 0] := by
  rw [torusMapMatrix_comp, torusMapMatrix_torusFst, torusMapMatrix_torusSwap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem torusMapMatrix_swap_circleMapTorus (v : C(Circle, Circle)) :
    torusMapMatrix (torusSwap.comp (circleMapTorus v)) = !![0, 0; circleDegree v, 0] := by
  rw [torusMapMatrix_comp, torusMapMatrix_torusSwap, torusMapMatrix_circleMapTorus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def fiberTorus (P : ProductFibredPiece T i k) : C(T.components.piece i, Torus) :=
  ⟨fun y => ((P.trivialization.symm y).2, 1),
    (continuous_snd.comp P.trivialization.symm.continuous).prodMk continuous_const⟩

def baseTorus (P : ProductFibredPiece T i k) (g : C(P.base.surface.Carrier, Circle)) :
    C(T.components.piece i, Torus) :=
  ⟨fun y => (g (P.trivialization.symm y).1, 1),
    (g.continuous.comp (continuous_fst.comp P.trivialization.symm.continuous)).prodMk
      continuous_const⟩

def baseTorusSnd (P : ProductFibredPiece T i k) (g : C(P.base.surface.Carrier, Circle)) :
    C(T.components.piece i, Torus) :=
  ⟨fun y => (1, g (P.trivialization.symm y).1),
    continuous_const.prodMk (g.continuous.comp
      (continuous_fst.comp P.trivialization.symm.continuous))⟩

theorem fiberTorus_comp_portMap (P : ProductFibredPiece T i k) (a : Fin k) :
    P.fiberTorus.comp (P.portMap a) = torusFst.comp torusSwap := by
  ext x <;> simp [fiberTorus, portMap_apply, torusFst, torusSwap]

theorem baseTorus_comp_portMap (P : ProductFibredPiece T i k)
    (g : C(P.base.surface.Carrier, Circle)) (a : Fin k) :
    (P.baseTorus g).comp (P.portMap a) = circleMapTorus (g.comp (P.base.boundaryCircle a)) := by
  ext x <;> simp [baseTorus, portMap_apply, circleMapTorus]

theorem baseTorusSnd_comp_portMap (P : ProductFibredPiece T i k)
    (g : C(P.base.surface.Carrier, Circle)) (a : Fin k) :
    (P.baseTorusSnd g).comp (P.portMap a) =
      torusSwap.comp (circleMapTorus (g.comp (P.base.boundaryCircle a))) := by
  ext x <;> simp [baseTorusSnd, portMap_apply, circleMapTorus, torusSwap]

def solidTheta (P : ProductFibredPiece T i k) (e : ℤ) : C(T.components.piece i, Torus) :=
  P.fiberTorus ^ e

theorem torusMapMatrix_solidTheta_comp (P : ProductFibredPiece T i k) (e : ℤ) (a : Fin k) :
    torusMapMatrix ((P.solidTheta e).comp (P.portMap a)) = !![0, e; 0, 0] := by
  rw [solidTheta, ContinuousMap.zpow_comp, fiberTorus_comp_portMap, torusMapMatrix_zpow,
    torusMapMatrix_fiberDirection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def productTheta (P : ProductFibredPiece T i k) (hk : k = 3) (f : Fin k) (p q : ℤ) :
    C(T.components.piece i, Torus) :=
  P.baseTorus (P.base.boundaryRetraction (by omega) f) ^ (-q) * P.fiberTorus ^ p *
    P.baseTorusSnd (P.base.pantsTransverse hk f)

theorem torusMapMatrix_productTheta_comp (P : ProductFibredPiece T i k) (hk : k = 3)
    (f a : Fin k) (p q : ℤ) :
    torusMapMatrix ((P.productTheta hk f p q).comp (P.portMap a)) =
      !![-q * circleDegree ((P.base.boundaryRetraction (by omega) f).comp
          (P.base.boundaryCircle a)), p;
        circleDegree ((P.base.pantsTransverse hk f).comp (P.base.boundaryCircle a)), 0] := by
  rw [productTheta, ContinuousMap.mul_comp, ContinuousMap.mul_comp, ContinuousMap.zpow_comp,
    ContinuousMap.zpow_comp, baseTorus_comp_portMap, fiberTorus_comp_portMap,
    baseTorusSnd_comp_portMap, torusMapMatrix_mul, torusMapMatrix_mul, torusMapMatrix_zpow,
    torusMapMatrix_zpow, torusMapMatrix_circleMapTorus, torusMapMatrix_fiberDirection,
    torusMapMatrix_swap_circleMapTorus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end ProductFibredPiece

end Theta

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem isGoodBlock_of_one_filling (B : SeifertBlock W d) (hk : d.k = 3)
    (hd : d.fillingCount = 1) : B.IsGoodBlock := by
  let m : Fin d.fillingCount := ⟨0, by omega⟩
  let M := torusMatrix (B.presentation.pairing.matching (B.seam m))
  let p := (d.fillingSlope m).1
  let q := (d.fillingSlope m).2
  let f := B.port (.inr m)
  refine B.isGoodBlock_of_fillingCount_eq_one hd ((B.solid m).solidTheta (p * M 1 1 - q * M 0 1))
    (B.product.productTheta hk f p q) ?_ fun r => ?_
  · rw [ProductFibredPiece.torusMapMatrix_solidTheta_comp,
      ProductFibredPiece.torusMapMatrix_productTheta_comp,
      B.product.base.circleDegree_retraction_self,
      (B.product.base.circleDegree_pantsTransverse hk f f).2 rfl]
    have hmer := B.torusMatrix_meridian m
    ext i j
    fin_cases i <;> fin_cases j
    · rcases hmer with h | h <;> simp only [Prod.ext_iff, Prod.fst_neg, Prod.snd_neg] at h <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, p, q, m, h.1, h.2, mul_comm]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [ProductFibredPiece.torusMapMatrix_productTheta_comp, Matrix.det_fin_two_of]
    have hne : B.port (.inl r) ≠ f := fun h => Sum.inl_ne_inr (B.port.injective h)
    have hdeg := (B.product.base.circleDegree_pantsTransverse hk f (B.port (.inl r))).not.2 hne
    have hp : 0 < p := d.fillingSlope_fst_pos m
    simp only [mul_zero, zero_sub, neg_ne_zero, mul_ne_zero_iff]
    exact ⟨hp.ne', hdeg⟩

theorem isGoodBlock_of_fillingCount_le_one (B : SeifertBlock W d) (hports : 0 < d.ports)
    (hst : ¬ d.IsSolidTorus) (h1 : d.fillingCount ≤ 1) : B.IsGoodBlock := by
  have hk := d.ports_add_fillingCount
  have hk3 := d.k_le_three
  have hc : d.cones.length ≤ d.fillingCount := Nat.le_add_right _ _
  simp only [SeifertData.IsSolidTorus, not_and, not_le] at hst
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0
  · refine B.isGoodBlock_of_fillingCount_eq_zero ?_ h0
    by_contra hlt
    have := hst (by omega)
    omega
  · refine B.isGoodBlock_of_one_filling ?_ h0
    by_contra hne
    have := hst (by omega)
    omega

end SeifertBlock

end GC.Seifert
