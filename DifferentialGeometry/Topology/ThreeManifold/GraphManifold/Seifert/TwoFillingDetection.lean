import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TwoFillings
import DifferentialGeometry.Topology.FundamentalGroup.CirclePowerDegree

/-!
# Detection of two-filling blocks

Chapter 6, packet K10e: `TwoFillingDetection` for every Seifert block with two genuine cone
fillings, hence `FilledBlockGoodness` unconditionally.

Marked maps. `forall_conj_push`, `forall_conj_comp`, `forall_conj_pull`, `forall_conj_congr`,
`forall_conj_comp_torus` and `forall_conj_changeBasepoint` move statements of the form "for every
marking path, the homomorphism on the marked map is `E` up to one conjugation" along inclusions,
compositions, torus maps and basepoint changes. `circleHom ρ` reads π₁ through a circle-valued
map; its value on a marked map is that of the composite (`circleHom_markedMap_eq`), on the second
torus coordinate it is the second coordinate (`circleHom_snd`), and it vanishes for a map into an
open half circle (`circleHom_eq_one`).

Pants. On the plane minus the two hole centres, van Kampen on `{Re < 1/2} ∪ {Re > -1/2}` (convex
overlap) with the two hole retractions gives, for any `u v` in a group, a homomorphism sending
the holes to `u`, `v` and the outer circle to `(v u)⁻¹`, up to conjugacy, for every marking path
(`PlanarBase.exists_pantsHom`); there is no detour through a free group.

Regions. A solid torus owns only the left side of its seam, so its image meets the rest of `W`
only in the seam torus. Hence the left region of a filling seam retracts onto the solid torus
(`exists_leafRetraction`), and for two fillings the middle region `R₀ ∩ R₁` is the image of the
product piece together with the two collars (seam collars are disjoint, `seam_disjoint`), is
path-connected and retracts onto the product piece (`isPathConnected_middle`,
`exists_middleRetraction`). The retractions are built from `collarShrink` on closed covers
(`exists_collarShrink_ite`) and the embedding of a piece (`exists_pieceRetraction`).

Gluing. `exists_hom_glue_solid`: a homomorphism on one side of a cover whose value on the seam
torus is `y ^ (second coordinate)` extends over the union, the solid side being `y ^ deg` of the
fibre. The product piece maps to `F(a, b) × ℤ` by the pants homomorphism on the base and the fibre
degree (`productHom`); on a port it is `(w ^ m, n)` up to conjugacy (`productHom_port`). Composed
with `twoFillingIncl` into `TwoFillingGroup`, the meridian relation `a ^ p h ^ q = 1` comes from
the slope of the filling (`torusMatrix_meridian`, `incl_relation_of_slope`), and the seam value
is a power of one element (`seam_value`, `port_matching_value`). Van Kampen inside `R₀` along the
second seam (`exists_inner_hom`), then in `W` along the first (`exists_core_hom`), give a
homomorphism on π₁ of `W` sending the free port to `((ab)⁻¹) ^ m h ^ n`.

Results. `twoFillingDetection_of_fillingCount_eq_two` (two fillings and not a solid torus, i.e.
both fillings genuine cones; with a normal filling the block is a solid torus and the statement
fails), `isGoodBlock_of_twistedIBundle`, and `filledBlockGoodness`.
-/

set_option autoImplicit false

noncomputable section
open Set Multiplicative
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate unitInterval

universe u

namespace GC.Seifert

section Marked
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem changeBasepoint_map (f : C(X, Y)) {z m : X} (β : Path z m) (g : FundamentalGroup X m) :
    FundamentalGroup.map f z (fundamentalGroupChangeBasepoint β g) =
      fundamentalGroupChangeBasepoint (β.map f.continuous) (FundamentalGroup.map f m g) := by
  simp only [fundamentalGroupChangeBasepoint_apply, FundamentalGroup.map_apply]
  induction g using Path.Homotopic.Quotient.ind with | mk p => ?_
  have hq : ∀ {x y : X} (q : Path x y),
      (⟦q⟧ : Path.Homotopic.Quotient x y) = Path.Homotopic.Quotient.mk q := fun q => rfl
  have hq' : ∀ {x y : Y} (q : Path x y),
      (⟦q⟧ : Path.Homotopic.Quotient x y) = Path.Homotopic.Quotient.mk q := fun q => rfl
  simp only [hq, hq', ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans,
    ← Path.Homotopic.Quotient.mk_symm]
  simp only [Path.map_trans, Path.map_symm]

theorem map_comp_markedMap (f : C(X, Y)) (g : C(Y, Z)) (x : X) {y : Y} (γ : Path y (f x)) :
    (FundamentalGroup.map g y).comp (GC.Topology.markedMap f x γ) =
      GC.Topology.markedMap (g.comp f) x (γ.map g.continuous) := by
  ext a
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [changeBasepoint_map, GC.Topology.fundamentalGroup_map_comp]
  rfl

theorem markedMap_comp_markedMap (f : C(X, Y)) (g : C(Y, Z)) (x : X) {y : Y} {z : Z}
    (γ : Path y (f x)) (δ : Path z (g y)) :
    (GC.Topology.markedMap g y δ).comp (GC.Topology.markedMap f x γ) =
      GC.Topology.markedMap (g.comp f) x (δ.trans (γ.map g.continuous)) := by
  ext a
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [changeBasepoint_map, ← changeBasepoint_trans, GC.Topology.fundamentalGroup_map_comp]
  rfl

theorem markedMap_refl (f : C(X, Y)) (x : X) :
    GC.Topology.markedMap f x (Path.refl (f x)) = FundamentalGroup.map f x := by
  ext a
  exact changeBasepoint_refl _

theorem markedMap_trans (f : C(X, Y)) (x : X) {y y' : Y} (β : Path y y') (γ : Path y' (f x))
    (a : FundamentalGroup X x) :
    GC.Topology.markedMap f x (β.trans γ) a =
      fundamentalGroupChangeBasepoint β (GC.Topology.markedMap f x γ a) :=
  changeBasepoint_trans β γ _

variable {G : Type*} [Group G]

theorem exists_conj_markedMap {x : X} (F : FundamentalGroup X x →* G) (f : C(Y, X)) (y : Y)
    (δ δ' : Path x (f y)) : ∃ k : G, ∀ a,
      F (GC.Topology.markedMap f y δ' a) = k * F (GC.Topology.markedMap f y δ a) * k⁻¹ := by
  refine ⟨(F (connectorLoop δ δ'))⁻¹, fun a => ?_⟩
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [fundamentalGroupChangeBasepoint_connector δ δ', MulAut.conj_apply]
  simp only [map_mul, map_inv, inv_inv]

theorem forall_conj_of_exists {x : X} (F : FundamentalGroup X x →* G) (f : C(Y, X)) (y : Y)
    (E : FundamentalGroup Y y → G)
    (h : ∃ δ : Path x (f y), ∃ k : G, ∀ a, F (GC.Topology.markedMap f y δ a) = k * E a * k⁻¹) :
    ∀ δ : Path x (f y), ∃ k : G, ∀ a, F (GC.Topology.markedMap f y δ a) = k * E a * k⁻¹ := by
  obtain ⟨δ₀, k₀, h₀⟩ := h
  intro δ
  obtain ⟨k, hk⟩ := exists_conj_markedMap F f y δ₀ δ
  refine ⟨k * k₀, fun a => ?_⟩
  rw [hk, h₀]
  group

theorem forall_conj_push {T : Type*} [TopologicalSpace T] (i : C(Y, X)) (y₀ : Y)
    (F : FundamentalGroup X (i y₀) →* G) (FY : FundamentalGroup Y y₀ →* G)
    (hF : F.comp (FundamentalGroup.map i y₀) = FY) (g : C(T, Y)) (t : T) (δ₀ : Path y₀ (g t))
    (E : FundamentalGroup T t → G)
    (h : ∀ δ : Path y₀ (g t), ∃ k : G, ∀ a,
      FY (GC.Topology.markedMap g t δ a) = k * E a * k⁻¹) :
    ∀ δ : Path (i y₀) ((i.comp g) t), ∃ k : G, ∀ a,
      F (GC.Topology.markedMap (i.comp g) t δ a) = k * E a * k⁻¹ := by
  refine forall_conj_of_exists F _ t E ⟨δ₀.map i.continuous, ?_⟩
  obtain ⟨k, hk⟩ := h δ₀
  refine ⟨k, fun a => ?_⟩
  rw [← map_comp_markedMap, MonoidHom.comp_apply, ← MonoidHom.comp_apply F, hF]
  exact hk a

theorem forall_conj_comp {W' T : Type*} [TopologicalSpace W'] [TopologicalSpace T] {w : W'}
    (F : FundamentalGroup W' w →* G) (g : C(Y, W')) (y₀ : Y) (β : Path w (g y₀))
    (f : C(T, Y)) (t : T) (E : FundamentalGroup T t → G)
    (h : ∀ δ : Path w ((g.comp f) t), ∃ k : G, ∀ a,
      F (GC.Topology.markedMap (g.comp f) t δ a) = k * E a * k⁻¹) :
    ∀ δ : Path y₀ (f t), ∃ k : G, ∀ a,
      (F.comp (GC.Topology.markedMap g y₀ β)) (GC.Topology.markedMap f t δ a) =
        k * E a * k⁻¹ := by
  intro δ
  obtain ⟨k, hk⟩ := h (β.trans (δ.map g.continuous))
  refine ⟨k, fun a => ?_⟩
  rw [MonoidHom.comp_apply, ← MonoidHom.comp_apply (GC.Topology.markedMap g y₀ β),
    markedMap_comp_markedMap]
  exact hk a

end Marked

section CircleTools

theorem fundamentalGroup_map_eq_one_of_homotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : C(X, Y)} (c : Y) (H : f.Homotopy (ContinuousMap.const X c))
    (x : X) {y : Y} (β : Path y (f x)) (a : FundamentalGroup X x) :
    GC.Topology.markedMap f x β a = 1 := by
  have h := congrArg (fun φ => φ a) (GC.Topology.homotopy_track f _ H x)
  have h1 : FundamentalGroup.map f x a = 1 := by
    rw [← h]
    simp only [GC.Topology.markedMap, MonoidHom.comp_apply, fundamentalGroup_map_const, map_one]
  simp only [GC.Topology.markedMap, MonoidHom.comp_apply, h1, map_one]

def circleInc : C(Circle, Torus) := ⟨fun t => (t, 1), by fun_prop⟩

theorem toAdd_torusCoordinates_circleInc (b : FundamentalGroup Circle 1) :
    toAdd (torusCoordinates (FundamentalGroup.map circleInc 1 b)) =
      ![toAdd (fundamentalGroupCircleEquivInt b), 0] := by
  refine (toAdd_torusCoordinates _).trans ?_
  have h1 : FundamentalGroup.map ContinuousMap.fst torusBase
      (FundamentalGroup.map circleInc 1 b) = b := by
    induction b using Path.Homotopic.Quotient.ind
    rfl
  have h2 : FundamentalGroup.map ContinuousMap.snd torusBase
      (FundamentalGroup.map circleInc 1 b) = 1 := by
    refine Eq.trans ?_ (fundamentalGroup_map_const (1 : Circle) (1 : Circle) b)
    induction b using Path.Homotopic.Quotient.ind
    rfl
  rw [h1, h2]
  ext i
  fin_cases i
  · rfl
  · exact congrArg toAdd (map_one fundamentalGroupCircleEquivInt)

theorem circleInt_markedMap (u : C(Circle, Circle)) (β : Path 1 (u 1))
    (a : FundamentalGroup Circle 1) :
    toAdd (fundamentalGroupCircleEquivInt (GC.Topology.markedMap u 1 β a)) =
      circleDegree u * toAdd (fundamentalGroupCircleEquivInt a) := by
  have key : torusAut (circleMapTorus u) (FundamentalGroup.map circleInc 1 a) =
      FundamentalGroup.map circleInc 1 (GC.Topology.markedMap u 1 β a) := by
    let γ : Path torusBase (circleMapTorus u torusBase) := β.map circleInc.continuous
    have h1 := DFunLike.congr_fun (markedMap_comp_map circleInc (circleMapTorus u) 1 γ) a
    have h2 := DFunLike.congr_fun (map_comp_markedMap u circleInc 1 β) a
    rw [torusAut_eq _ γ]
    exact h1.trans h2.symm
  have hm := torusMapMatrix_mulVec (circleMapTorus u) (FundamentalGroup.map circleInc 1 a)
  rw [key, toAdd_torusCoordinates_circleInc, toAdd_torusCoordinates_circleInc,
    torusMapMatrix_circleMapTorus] at hm
  have h0 := congrFun hm 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  exact h0.symm

theorem circleDegree_comp (f g : C(Circle, Circle)) :
    circleDegree (f.comp g) = circleDegree f * circleDegree g := by
  have h : circleMapTorus (f.comp g) = (circleMapTorus f).comp (circleMapTorus g) := by
    ext x <;> rfl
  rw [circleDegree, h, torusMapMatrix_comp, torusMapMatrix_circleMapTorus,
    torusMapMatrix_circleMapTorus]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

def circleRotate (c : Circle) : C(Circle, Circle) := ⟨fun t => c * t, by fun_prop⟩

theorem circleDegree_circleRotate (c : Circle) : circleDegree (circleRotate c) = 1 := by
  let γ := PathConnectedSpace.somePath (1 : Circle) c
  let H : C(I × Circle, Circle) := ⟨fun p => γ p.1 * p.2, by fun_prop⟩
  rw [← circleDegree_id]
  exact (circleDegree_eq_of_family H (fun t => by simp [H]) (fun t => by
    simp [H, circleRotate])).symm

def circleLoop : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * Real.pi * t)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem circleInt_circleLoop :
    fundamentalGroupCircleEquivInt (FundamentalGroup.fromPath ⟦circleLoop⟧) = ofAdd 1 := by
  have h := fundamentalGroupCircleEquivInt_map_addCircle
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath))
  rw [fundamentalGroupUnitAddCircleEquivInt_generator] at h
  rw [← h]
  congr 1
  simp only [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  change Circle.exp (2 * Real.pi * t) = AddCircle.homeomorphCircle _ (circleGeneratorPath t)
  rw [AddCircle.homeomorphCircle_apply]
  change _ = AddCircle.toCircle ((t : ℝ) : AddCircle (1 : ℝ))
  rw [AddCircle.toCircle_apply_mk, div_one]

theorem eq_circleLoop_zpow (a : FundamentalGroup Circle 1) :
    a = FundamentalGroup.fromPath ⟦circleLoop⟧ ^ toAdd (fundamentalGroupCircleEquivInt a) := by
  apply fundamentalGroupCircleEquivInt.injective
  rw [map_zpow, circleInt_circleLoop, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]

end CircleTools

section PlanePaths

theorem isPathConnected_diff_singleton {K : Set ℂ} (hK : Convex ℝ K) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hS : Metric.sphere c r ⊆ K) : IsPathConnected (K \ {c}) := by
  have hSP : IsPathConnected (Metric.sphere c r) :=
    isPathConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c hr.le
  have hSK : Metric.sphere c r ⊆ K \ {c} := fun z hz => ⟨hS hz, fun h => by
    rw [Set.mem_singleton_iff] at h
    rw [h, Metric.mem_sphere, dist_self] at hz
    exact hr.ne' hz.symm⟩
  obtain ⟨b, hb⟩ := hSP.nonempty
  refine ⟨b, hSK hb, fun y hy => ?_⟩
  have hyc : y - c ≠ 0 := sub_ne_zero.2 hy.2
  have hn : 0 < ‖y - c‖ := norm_pos_iff.2 hyc
  set p : ℂ := c + ((r / ‖y - c‖ : ℝ) : ℂ) * (y - c) with hp_def
  have hp : p ∈ Metric.sphere c r := by
    rw [Metric.mem_sphere, dist_eq_norm, hp_def, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (div_nonneg hr.le hn.le), div_mul_cancel₀ _ hn.ne']
  refine ((hSP.joinedIn b hb p hp).mono hSK).trans ⟨Path.segment p y, fun t => ?_⟩
  have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t.2
  change AffineMap.lineMap p y (t : ℝ) ∈ K \ {c}
  refine ⟨hK.lineMap_mem (hS hp) hy.1 ht, fun h => ?_⟩
  rw [Set.mem_singleton_iff, AffineMap.lineMap_apply_module'] at h
  have hl : 0 < (1 - (t : ℝ)) * (r / ‖y - c‖) + t := by
    have hq : 0 < r / ‖y - c‖ := div_pos hr hn
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]
      linarith
    · nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hq.le]
  have h2 : ((((1 - (t : ℝ)) * (r / ‖y - c‖) + t : ℝ) : ℂ)) * (y - c) = 0 := by
    rw [← sub_eq_zero.2 h, hp_def]
    simp only [Complex.real_smul]
    push_cast
    ring
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hl.ne' (Complex.ofReal_eq_zero.1 h3)
  · exact hyc h3

end PlanePaths

section CircleHom
variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']

def circleHom (ρ : C(Y, Circle)) (y : Y) : FundamentalGroup Y y →* Multiplicative ℤ :=
  fundamentalGroupCircleEquivInt.toMonoidHom.comp
    (GC.Topology.markedMap ρ y (PathConnectedSpace.somePath 1 (ρ y)))

theorem circleHom_markedMap (ρ : C(Y, Circle)) (y : Y) (f : C(Circle, Y)) (β : Path y (f 1))
    (a : FundamentalGroup Circle 1) :
    toAdd (circleHom ρ y (GC.Topology.markedMap f 1 β a)) =
      circleDegree (ρ.comp f) * toAdd (fundamentalGroupCircleEquivInt a) := by
  rw [circleHom, MonoidHom.comp_apply, ← MonoidHom.comp_apply (GC.Topology.markedMap ρ y _),
    markedMap_comp_markedMap]
  exact circleInt_markedMap _ _ a

theorem circleHom_map (ρ : C(Y, Circle)) (i : C(Y', Y)) (y : Y') (a : FundamentalGroup Y' y) :
    circleHom ρ (i y) (FundamentalGroup.map i y a) = circleHom (ρ.comp i) y a := by
  simp only [circleHom, MonoidHom.comp_apply]
  exact congrArg _ (DFunLike.congr_fun (markedMap_comp_map i ρ y _) a)

theorem circleHom_eq_one (f : C(Y, Circle)) (c : Circle)
    (hf : ∀ y, 0 < ((f y : ℂ) * conj (c : ℂ)).re) (y : Y) (a : FundamentalGroup Y y) :
    circleHom f y a = 1 := by
  have hc : ((c : ℂ) * conj (c : ℂ)).re = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    simp
  let V : I × Y → ℂ := fun p => ((1 - (p.1 : ℝ) : ℝ) : ℂ) * f p.2 + ((p.1 : ℝ) : ℂ) * c
  have hV : Continuous V := by fun_prop
  have h0 : ∀ p, V p ≠ 0 := by
    intro p hp
    have h := congrArg (fun w => (w * conj (c : ℂ)).re) hp
    have h1 := hf p.2
    have hs0 := p.1.2.1
    have hs1 := p.1.2.2
    simp only [V, add_mul, mul_assoc, Complex.add_re, Complex.re_ofReal_mul, zero_mul,
      Complex.zero_re] at h
    rw [hc] at h
    rcases eq_or_lt_of_le hs0 with he | hlt
    · rw [← he] at h
      simp [Complex.mul_re] at h h1
      linarith
    · nlinarith [mul_nonneg (sub_nonneg.2 hs1) h1.le]
  let H : f.Homotopy (ContinuousMap.const Y c) :=
    { toFun := circleNormalize V hV h0
      continuous_toFun := (circleNormalize V hV h0).continuous
      map_zero_left := fun y => by
        apply Circle.coe_injective
        simp [coe_circleNormalize, V]
      map_one_left := fun y => by
        apply Circle.coe_injective
        simp [coe_circleNormalize, V] }
  rw [circleHom, MonoidHom.comp_apply, fundamentalGroup_map_eq_one_of_homotopy c H y _ a,
    map_one]

end CircleHom

section PantsModel

def pantsPlane : Set ℂ := {z | z ≠ 3 / 2 ∧ z ≠ -(3 / 2)}

abbrev PantsPlane := ↥pantsPlane

theorem planarModel_subset_pantsPlane : planarModel 3 ⊆ pantsPlane := by
  intro z hz
  have h1 := hz.2 1 (by decide)
  have h2 := hz.2 2 (by decide)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1
    norm_num [planarCenter] at h1
  · rw [h] at h2
    norm_num [planarCenter] at h2

theorem mem_pantsPlane_of_norm (z : ℂ) (hz : ‖z‖ = 3) : z ∈ pantsPlane := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at hz <;> norm_num at hz

theorem mem_pantsPlane_of_re (z : ℂ) (hz : z.re = 0) : z ∈ pantsPlane := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at hz <;> norm_num at hz

theorem planarRetractionVector_ne_zero_of_mem {j : Fin 3} (hj : j.val ≠ 0) (x : PantsPlane) :
    planarRetractionVector 3 j x.1 ≠ 0 := by
  unfold planarRetractionVector
  split_ifs with h
  · exact absurd h hj
  rw [map_ne_zero, sub_ne_zero]
  fin_cases j
  · exact absurd rfl hj
  · have := x.2.1
    norm_num [planarCenter]
    exact this
  · have := x.2.2
    norm_num [planarCenter]
    exact this

def pantsRetraction (j : Fin 3) (hj : j.val ≠ 0) : C(PantsPlane, Circle) :=
  circleNormalize (fun x => planarRetractionVector 3 j x.1)
    ((continuous_planarRetractionVector 3 j).comp continuous_subtype_val)
    (planarRetractionVector_ne_zero_of_mem hj)

theorem continuous_planarCircleMap (k : ℕ) (j : Fin k) : Continuous (planarCircleMap k j) := by
  unfold planarCircleMap
  split_ifs <;> fun_prop

def pantsCircle (j : Fin 3) : C(Circle, PantsPlane) :=
  ⟨fun t => ⟨planarCircleMap 3 j t,
    planarModel_subset_pantsPlane (planarCircleMap_mem_planarModel le_rfl j t)⟩,
    (continuous_planarCircleMap 3 j).subtype_mk _⟩

theorem pantsRetraction_comp_pantsCircle (j : Fin 3) (hj : j.val ≠ 0) :
    (pantsRetraction j hj).comp (pantsCircle j) = ContinuousMap.id Circle := by
  refine ContinuousMap.ext fun t => Circle.coe_injective ?_
  obtain ⟨a, ha, h⟩ := planarRetractionVector_planarCircleMap 3 j t
  change planarRetractionVector 3 j (planarCircleMap 3 j t) /
    (‖planarRetractionVector 3 j (planarCircleMap 3 j t)‖ : ℂ) = t
  rw [h]
  exact circleNormalize_real_mul ha (Circle.norm_coe t)

def pantsLeft : Set PantsPlane := {x | x.1.re < 1 / 2}

def pantsRight : Set PantsPlane := {x | -(1 / 2) < x.1.re}

theorem isOpen_pantsLeft : IsOpen pantsLeft :=
  isOpen_lt (Complex.continuous_re.comp continuous_subtype_val) continuous_const

theorem isOpen_pantsRight : IsOpen pantsRight :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)

theorem pantsLeft_union_pantsRight : pantsLeft ∪ pantsRight = univ := by
  refine eq_univ_of_forall fun x => ?_
  by_cases h : x.1.re < 1 / 2
  · exact Or.inl h
  · exact Or.inr (show -(1 / 2) < x.1.re by linarith)

theorem isPathConnected_pantsLeft : IsPathConnected pantsLeft := by
  have hK : Convex ℝ {z : ℂ | z.re < 1 / 2} := convex_halfSpace_lt Complex.reLm.isLinear _
  have hS : Metric.sphere (-(3 / 2) : ℂ) (1 / 2) ⊆ {z : ℂ | z.re < 1 / 2} := by
    intro z hz
    have h := Complex.re_le_norm (z - (-(3 / 2)))
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    rw [hz] at h
    simp only [Complex.sub_re, Complex.neg_re] at h
    norm_num at h
    change z.re < 1 / 2
    linarith
  have hsub : {z : ℂ | z.re < 1 / 2} \ {-(3 / 2)} ⊆ pantsPlane := by
    rintro z ⟨hz, hz'⟩
    refine ⟨fun h => ?_, hz'⟩
    rw [h] at hz
    norm_num at hz
  have h := (isPathConnected_diff_singleton hK (by norm_num) hS).preimage_coe hsub
  convert h using 1
  ext x
  exact ⟨fun hx => ⟨hx, x.2.2⟩, fun hx => hx.1⟩

theorem isPathConnected_pantsRight : IsPathConnected pantsRight := by
  have hK : Convex ℝ {z : ℂ | -(1 / 2) < z.re} := convex_halfSpace_gt Complex.reLm.isLinear _
  have hS : Metric.sphere (3 / 2 : ℂ) (1 / 2) ⊆ {z : ℂ | -(1 / 2) < z.re} := by
    intro z hz
    have h := Complex.abs_re_le_norm (z - 3 / 2)
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    rw [hz] at h
    simp only [Complex.sub_re] at h
    norm_num at h
    have := (abs_le.1 h).1
    change -(1 / 2) < z.re
    linarith
  have hsub : {z : ℂ | -(1 / 2) < z.re} \ {3 / 2} ⊆ pantsPlane := by
    rintro z ⟨hz, hz'⟩
    refine ⟨hz', fun h => ?_⟩
    rw [h] at hz
    norm_num at hz
  have h := (isPathConnected_diff_singleton hK (by norm_num) hS).preimage_coe hsub
  convert h using 1
  ext x
  exact ⟨fun hx => ⟨hx, x.2.1⟩, fun hx => hx.1⟩

instance pathConnectedSpace_pantsLeft : PathConnectedSpace pantsLeft :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pantsLeft

instance pathConnectedSpace_pantsRight : PathConnectedSpace pantsRight :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pantsRight

def pantsStrip : Set ℂ := {z | z.re < 1 / 2} ∩ {z | -(1 / 2) < z.re}

theorem pantsStrip_subset : pantsStrip ⊆ pantsPlane := by
  rintro z ⟨h1, h2⟩
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at h1 h2
  · norm_num at h1
  · norm_num at h2

def pantsOverlapHomeomorph : ↥(pantsLeft ∩ pantsRight) ≃ₜ ↥pantsStrip where
  toFun x := ⟨x.1.1, x.2.1, x.2.2⟩
  invFun z := ⟨⟨z.1, pantsStrip_subset z.2⟩, z.2.1, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

instance contractibleSpace_pantsOverlap : ContractibleSpace ↥(pantsLeft ∩ pantsRight) := by
  have hc : Convex ℝ pantsStrip := (convex_halfSpace_lt Complex.reLm.isLinear _).inter
    (convex_halfSpace_gt Complex.reLm.isLinear _)
  have : ContractibleSpace ↥pantsStrip := hc.contractibleSpace ⟨0, by norm_num [pantsStrip]⟩
  exact pantsOverlapHomeomorph.contractibleSpace

instance pathConnectedSpace_pantsPlane : PathConnectedSpace PantsPlane := by
  rw [pathConnectedSpace_iff_univ, ← pantsLeft_union_pantsRight]
  refine isPathConnected_pantsLeft.union isPathConnected_pantsRight ⟨⟨0, ?_⟩, ?_, ?_⟩
  · exact mem_pantsPlane_of_re 0 rfl
  · change (0 : ℂ).re < 1 / 2
    norm_num
  · change -(1 / 2) < (0 : ℂ).re
    norm_num

end PantsModel

section PantsHom

open DifferentialGeometry.Topology.VanKampen

def pantsRetractionRight : C(PantsPlane, Circle) := pantsRetraction 1 (by decide)

def pantsRetractionLeft : C(PantsPlane, Circle) := pantsRetraction 2 (by decide)

theorem re_coe_pantsRetraction (j : Fin 3) (hj : j.val ≠ 0) (x : PantsPlane) :
    (pantsRetraction j hj x : ℂ).re =
      (x.1.re - planarCenter 3 j) / ‖x.1 - planarCenter 3 j‖ := by
  change (planarRetractionVector 3 j x.1 / (‖planarRetractionVector 3 j x.1‖ : ℂ)).re = _
  simp only [planarRetractionVector, hj, ↓reduceIte, Complex.norm_conj, Complex.div_ofReal_re,
    Complex.conj_re, Complex.sub_re, Complex.ofReal_re]

theorem norm_sub_planarCenter_pos (j : Fin 3) (hj : j.val ≠ 0) (x : PantsPlane) :
    0 < ‖x.1 - planarCenter 3 j‖ := by
  have h := planarRetractionVector_ne_zero_of_mem hj x
  simp only [planarRetractionVector, hj, ↓reduceIte, map_ne_zero] at h
  exact norm_pos_iff.2 h

theorem circleHom_pantsRetractionRight_left (y : pantsLeft) (a : FundamentalGroup pantsLeft y) :
    circleHom (pantsRetractionRight.comp (subsetToAmbient pantsLeft)) y a = 1 := by
  refine circleHom_eq_one _ (Circle.exp Real.pi) (fun x => ?_) y a
  have hc : ((Circle.exp Real.pi : Circle) : ℂ) = -1 := by
    rw [Circle.coe_exp]
    exact Complex.exp_pi_mul_I
  have hre := re_coe_pantsRetraction 1 (by decide) x.1
  have hn := norm_sub_planarCenter_pos 1 (by decide) x.1
  have hx : x.1.1.re < 1 / 2 := x.2
  change 0 < ((pantsRetraction 1 (by decide) x.1 : ℂ) * conj ((Circle.exp Real.pi : Circle) : ℂ)).re
  rw [hc, map_neg, map_one, mul_neg_one, Complex.neg_re, hre]
  have hp : planarCenter 3 1 = 3 / 2 := by norm_num [planarCenter]
  rw [hp] at hn ⊢
  have : (x.1.1.re - 3 / 2) / ‖x.1.1 - ((3 / 2 : ℝ) : ℂ)‖ < 0 :=
    div_neg_of_neg_of_pos (by linarith) hn
  linarith

theorem circleHom_pantsRetractionLeft_right (y : pantsRight) (a : FundamentalGroup pantsRight y) :
    circleHom (pantsRetractionLeft.comp (subsetToAmbient pantsRight)) y a = 1 := by
  refine circleHom_eq_one _ 1 (fun x => ?_) y a
  have hre := re_coe_pantsRetraction 2 (by decide) x.1
  have hn := norm_sub_planarCenter_pos 2 (by decide) x.1
  have hx : -(1 / 2) < x.1.1.re := x.2
  change 0 < ((pantsRetraction 2 (by decide) x.1 : ℂ) * conj ((1 : Circle) : ℂ)).re
  rw [Circle.coe_one, map_one, mul_one, hre]
  have hp : planarCenter 3 2 = -(3 / 2) := by norm_num [planarCenter]
  rw [hp] at hn ⊢
  exact div_pos (by linarith) hn

def pantsQuarter : Circle := Circle.exp (Real.pi / 2)

theorem coe_pantsQuarter : (pantsQuarter : ℂ) = Complex.I := by
  unfold pantsQuarter
  rw [Circle.coe_exp]
  push_cast
  exact Complex.exp_pi_div_two_mul_I

def pantsOuter : C(Circle, PantsPlane) := (pantsCircle 0).comp (circleRotate pantsQuarter)

theorem coe_pantsOuter (t : Circle) : ((pantsOuter t : PantsPlane) : ℂ) = 3 * Complex.I * t := by
  change planarCircleMap 3 0 (pantsQuarter * t) = _
  simp [planarCircleMap, planarCenter, planarRadius, coe_pantsQuarter]
  ring

theorem re_pantsOuter_one : ((pantsOuter 1 : PantsPlane) : ℂ).re = 0 := by
  rw [coe_pantsOuter]
  simp

abbrev pantsBase : ↥(pantsLeft ∩ pantsRight) :=
  ⟨pantsOuter 1,
    show ((pantsOuter 1 : PantsPlane) : ℂ).re < 1 / 2 by rw [re_pantsOuter_one]; norm_num,
    show -(1 / 2) < ((pantsOuter 1 : PantsPlane) : ℂ).re by rw [re_pantsOuter_one]; norm_num⟩

def pantsBot : PantsPlane := ⟨-(3 * Complex.I), mem_pantsPlane_of_re _ (by simp)⟩

def pantsStripBot : ↥(pantsLeft ∩ pantsRight) :=
  ⟨pantsBot, show (-(3 * Complex.I)).re < 1 / 2 by simp,
    show -(1 / 2) < (-(3 * Complex.I)).re by simp⟩

theorem norm_mul_exp_mul_I (c : ℂ) (θ : ℝ) : ‖c * Complex.exp (θ * Complex.I)‖ = ‖c‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem re_mul_exp_mul_I (c : ℂ) (θ : ℝ) :
    (c * Complex.exp (θ * Complex.I)).re = c.re * Real.cos θ - c.im * Real.sin θ := by
  rw [Complex.exp_mul_I]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem sin_pi_mul_nonneg (s : I) : 0 ≤ Real.sin (Real.pi * s) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le s.2.1)
    (mul_le_of_le_one_right Real.pi_pos.le s.2.2)

def pantsArcValue (c : ℂ) (s : I) : ℂ := c * Complex.exp ((Real.pi * s : ℝ) * Complex.I)

theorem continuous_pantsArcValue (c : ℂ) : Continuous (pantsArcValue c) := by
  unfold pantsArcValue
  fun_prop

theorem norm_pantsArcValue (c : ℂ) (s : I) : ‖pantsArcValue c s‖ = ‖c‖ :=
  norm_mul_exp_mul_I _ _

theorem re_pantsArcValue_top (s : I) : (pantsArcValue (3 * Complex.I) s).re < 1 / 2 := by
  rw [pantsArcValue, re_mul_exp_mul_I]
  have := sin_pi_mul_nonneg s
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  linarith

theorem re_pantsArcValue_bot (s : I) : -(1 / 2) < (pantsArcValue (-(3 * Complex.I)) s).re := by
  rw [pantsArcValue, re_mul_exp_mul_I]
  have := sin_pi_mul_nonneg s
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  norm_num
  linarith

theorem pantsArcValue_zero (c : ℂ) : pantsArcValue c 0 = c := by
  simp [pantsArcValue]

theorem pantsArcValue_one (c : ℂ) : pantsArcValue c 1 = -c := by
  simp [pantsArcValue, Complex.exp_pi_mul_I]

theorem coe_pantsBase : ((pantsBase.1 : PantsPlane) : ℂ) = 3 * Complex.I := by
  change ((pantsOuter 1 : PantsPlane) : ℂ) = _
  rw [coe_pantsOuter, Circle.coe_one, mul_one]

def pantsLeftArc : Path (interToLeft pantsLeft pantsRight pantsBase)
    (interToLeft pantsLeft pantsRight pantsStripBot) where
  toFun s := ⟨⟨pantsArcValue (3 * Complex.I) s, mem_pantsPlane_of_norm _ (by
    rw [norm_pantsArcValue]; simp)⟩, re_pantsArcValue_top s⟩
  continuous_toFun := ((continuous_pantsArcValue _).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (3 * Complex.I) 0 = ((pantsBase.1 : PantsPlane) : ℂ)
    rw [pantsArcValue_zero, coe_pantsBase]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (3 * Complex.I) 1 = -(3 * Complex.I)
    rw [pantsArcValue_one]

def pantsRightArc : Path (interToRight pantsLeft pantsRight pantsStripBot)
    (interToRight pantsLeft pantsRight pantsBase) where
  toFun s := ⟨⟨pantsArcValue (-(3 * Complex.I)) s, mem_pantsPlane_of_norm _ (by
    rw [norm_pantsArcValue]; simp)⟩, re_pantsArcValue_bot s⟩
  continuous_toFun := ((continuous_pantsArcValue _).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (-(3 * Complex.I)) 0 = -(3 * Complex.I)
    rw [pantsArcValue_zero]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsArcValue (-(3 * Complex.I)) 1 = ((pantsBase.1 : PantsPlane) : ℂ)
    rw [pantsArcValue_one, coe_pantsBase, neg_neg]

def pantsStripValue (s : I) : ℂ := ((6 * s - 3 : ℝ) : ℂ) * Complex.I

theorem re_pantsStripValue (s : I) : (pantsStripValue s).re = 0 := by
  simp [pantsStripValue]

def pantsStripPath : Path pantsStripBot pantsBase where
  toFun s := ⟨⟨pantsStripValue s, mem_pantsPlane_of_re _ (re_pantsStripValue s)⟩,
    show (pantsStripValue s).re < 1 / 2 by rw [re_pantsStripValue]; norm_num,
    show -(1 / 2) < (pantsStripValue s).re by rw [re_pantsStripValue]; norm_num⟩
  continuous_toFun := (((by unfold pantsStripValue; fun_prop :
    Continuous pantsStripValue).subtype_mk _).subtype_mk _)
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsStripValue 0 = -(3 * Complex.I)
    simp [pantsStripValue]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change pantsStripValue 1 = ((pantsBase.1 : PantsPlane) : ℂ)
    rw [coe_pantsBase]
    simp [pantsStripValue]
    norm_num

def pantsLoopLeft : Path (interToLeft pantsLeft pantsRight pantsBase)
    (interToLeft pantsLeft pantsRight pantsBase) :=
  pantsLeftArc.trans (pantsStripPath.map (interToLeft pantsLeft pantsRight).continuous)

def pantsLoopRight : Path (interToRight pantsLeft pantsRight pantsBase)
    (interToRight pantsLeft pantsRight pantsBase) :=
  (pantsStripPath.map (interToRight pantsLeft pantsRight).continuous).symm.trans pantsRightArc

def pantsLeftPath : Path pantsBase.1 pantsBot :=
  pantsLeftArc.map (subsetToAmbient pantsLeft).continuous

def pantsRightPath : Path pantsBot pantsBase.1 :=
  pantsRightArc.map (subsetToAmbient pantsRight).continuous

def pantsMidPath : Path pantsBot pantsBase.1 :=
  pantsStripPath.map (subsetToAmbient (pantsLeft ∩ pantsRight)).continuous

theorem pantsOuter_circleLoop :
    circleLoop.map pantsOuter.continuous = pantsLeftPath.trans pantsRightPath := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  · change ((pantsOuter (Circle.exp (2 * Real.pi * t)) : PantsPlane) : ℂ) =
      pantsArcValue (3 * Complex.I) _
    rw [coe_pantsOuter, Circle.coe_exp, pantsArcValue]
    push_cast
    ring_nf
  · change ((pantsOuter (Circle.exp (2 * Real.pi * t)) : PantsPlane) : ℂ) =
      pantsArcValue (-(3 * Complex.I)) _
    rw [coe_pantsOuter, Circle.coe_exp, pantsArcValue]
    have he : (((Real.pi * (2 * (t : ℝ) - 1) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) - (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_sub, Complex.exp_pi_mul_I]
    field_simp

theorem pantsOuter_map_circleLoop :
    FundamentalGroup.map pantsOuter 1 (FundamentalGroup.fromPath ⟦circleLoop⟧) =
      FundamentalGroup.fromPath ⟦pantsMidPath.symm.trans pantsRightPath⟧ *
        FundamentalGroup.fromPath ⟦pantsLeftPath.trans pantsMidPath⟧ := by
  rw [FundamentalGroup.mul_def]
  change (⟦circleLoop.map pantsOuter.continuous⟧ : Path.Homotopic.Quotient _ _) = _
  rw [pantsOuter_circleLoop]
  have hq : ∀ {x y : PantsPlane} (q : Path x y),
      (⟦q⟧ : Path.Homotopic.Quotient x y) = Path.Homotopic.Quotient.mk q := fun q => rfl
  simp only [hq, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk pantsMidPath)
    (Path.Homotopic.Quotient.mk pantsMidPath).symm, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

theorem map_pantsLoopLeft :
    @id (FundamentalGroup PantsPlane pantsBase.1) (FundamentalGroup.map
        (subsetToAmbient pantsLeft) _ (FundamentalGroup.fromPath ⟦pantsLoopLeft⟧)) =
      FundamentalGroup.fromPath ⟦pantsLeftPath.trans pantsMidPath⟧ := by
  change (⟦pantsLoopLeft.map (subsetToAmbient pantsLeft).continuous⟧ :
    Path.Homotopic.Quotient _ _) = _
  rw [pantsLoopLeft, Path.map_trans]
  rfl

theorem map_pantsLoopRight :
    @id (FundamentalGroup PantsPlane pantsBase.1) (FundamentalGroup.map
        (subsetToAmbient pantsRight) _ (FundamentalGroup.fromPath ⟦pantsLoopRight⟧)) =
      FundamentalGroup.fromPath ⟦pantsMidPath.symm.trans pantsRightPath⟧ := by
  change (⟦pantsLoopRight.map (subsetToAmbient pantsRight).continuous⟧ :
    Path.Homotopic.Quotient _ _) = _
  rw [pantsLoopRight, Path.map_trans, Path.map_symm]
  rfl

end PantsHom

section PantsKappa

open DifferentialGeometry.Topology.VanKampen

variable {G : Type*} [Group G]

def pantsLeftHom (v : G) :
    FundamentalGroup pantsLeft (interToLeft pantsLeft pantsRight pantsBase) →* G :=
  (zpowersHom G v).comp (circleHom (pantsRetractionLeft.comp (subsetToAmbient pantsLeft)) _)

def pantsRightHom (u : G) :
    FundamentalGroup pantsRight (interToRight pantsLeft pantsRight pantsBase) →* G :=
  (zpowersHom G u).comp (circleHom (pantsRetractionRight.comp (subsetToAmbient pantsRight)) _)

theorem exists_pantsPlaneHom (u v : G) :
    ∃ κ : FundamentalGroup PantsPlane pantsBase.1 →* G,
      κ.comp (FundamentalGroup.map (subsetToAmbient pantsLeft)
          (interToLeft pantsLeft pantsRight pantsBase)) = pantsLeftHom v ∧
        κ.comp (FundamentalGroup.map (subsetToAmbient pantsRight)
          (interToRight pantsLeft pantsRight pantsBase)) = pantsRightHom u :=
  exists_hom_of_openCover pantsLeft pantsRight isOpen_pantsLeft isOpen_pantsRight
    pantsLeft_union_pantsRight pantsBase _ _ (MonoidHom.ext fun g => by
      rw [Subsingleton.elim g 1, map_one, map_one])

theorem re_planarCircleMap_one (t : Circle) :
    (planarCircleMap 3 1 t).re = 3 / 2 + (t : ℂ).re / 2 := by
  simp [planarCircleMap, planarCenter, planarRadius]
  ring

theorem re_planarCircleMap_two (t : Circle) :
    (planarCircleMap 3 2 t).re = -(3 / 2) + (t : ℂ).re / 2 := by
  simp [planarCircleMap, planarCenter, planarRadius]
  ring

def pantsCircleRight : C(Circle, pantsRight) :=
  ⟨fun t => ⟨pantsCircle 1 t, show -(1 / 2) < (planarCircleMap 3 1 t).re by
    rw [re_planarCircleMap_one]
    have := (abs_le.1 ((Complex.abs_re_le_norm (t : ℂ)).trans_eq (Circle.norm_coe t))).1
    linarith⟩, (pantsCircle 1).continuous.subtype_mk _⟩

def pantsCircleLeft : C(Circle, pantsLeft) :=
  ⟨fun t => ⟨pantsCircle 2 t, show (planarCircleMap 3 2 t).re < 1 / 2 by
    rw [re_planarCircleMap_two]
    have := (abs_le.1 ((Complex.abs_re_le_norm (t : ℂ)).trans_eq (Circle.norm_coe t))).2
    linarith⟩, (pantsCircle 2).continuous.subtype_mk _⟩

theorem pantsHom_hole_right (u : G) (κ : FundamentalGroup PantsPlane pantsBase.1 →* G)
    (hR : κ.comp (FundamentalGroup.map (subsetToAmbient pantsRight)
      (interToRight pantsLeft pantsRight pantsBase)) = pantsRightHom u) :
    ∀ δ : Path pantsBase.1 (pantsCircle 1 1), ∃ k : G, ∀ a,
      κ (GC.Topology.markedMap (pantsCircle 1) 1 δ a) =
        k * u ^ toAdd (fundamentalGroupCircleEquivInt a) * k⁻¹ := by
  refine forall_conj_push (subsetToAmbient pantsRight)
    (interToRight pantsLeft pantsRight pantsBase) κ (pantsRightHom u) hR pantsCircleRight 1
    (PathConnectedSpace.somePath _ _) (fun a => u ^ toAdd (fundamentalGroupCircleEquivInt a))
    (fun δ => ⟨1, fun a => ?_⟩)
  have hc : (pantsRetractionRight.comp (subsetToAmbient pantsRight)).comp pantsCircleRight =
      ContinuousMap.id Circle :=
    pantsRetraction_comp_pantsCircle 1 (by decide)
  rw [pantsRightHom, MonoidHom.comp_apply, zpowersHom_apply, circleHom_markedMap, hc,
    circleDegree_id, one_mul, one_mul, inv_one, mul_one]

theorem pantsHom_hole_left (v : G) (κ : FundamentalGroup PantsPlane pantsBase.1 →* G)
    (hL : κ.comp (FundamentalGroup.map (subsetToAmbient pantsLeft)
      (interToLeft pantsLeft pantsRight pantsBase)) = pantsLeftHom v) :
    ∀ δ : Path pantsBase.1 (pantsCircle 2 1), ∃ k : G, ∀ a,
      κ (GC.Topology.markedMap (pantsCircle 2) 1 δ a) =
        k * v ^ toAdd (fundamentalGroupCircleEquivInt a) * k⁻¹ := by
  refine forall_conj_push (subsetToAmbient pantsLeft)
    (interToLeft pantsLeft pantsRight pantsBase) κ (pantsLeftHom v) hL pantsCircleLeft 1
    (PathConnectedSpace.somePath _ _) (fun a => v ^ toAdd (fundamentalGroupCircleEquivInt a))
    (fun δ => ⟨1, fun a => ?_⟩)
  have hc : (pantsRetractionLeft.comp (subsetToAmbient pantsLeft)).comp pantsCircleLeft =
      ContinuousMap.id Circle :=
    pantsRetraction_comp_pantsCircle 2 (by decide)
  rw [pantsLeftHom, MonoidHom.comp_apply, zpowersHom_apply, circleHom_markedMap, hc,
    circleDegree_id, one_mul, one_mul, inv_one, mul_one]

theorem circleDegree_pantsRetraction_pantsOuter (B : PlanarBase.{u} 3) (j : Fin 3)
    (hj : j.val ≠ 0) (hc : |planarCenter 3 j| < 3) :
    circleDegree ((pantsRetraction j hj).comp pantsOuter) = -1 := by
  have h1 : (pantsRetraction j hj).comp pantsOuter =
      ((pantsRetraction j hj).comp (pantsCircle 0)).comp (circleRotate pantsQuarter) := rfl
  have h2 : (pantsRetraction j hj).comp (pantsCircle 0) =
      (B.boundaryRetraction (by norm_num) j).comp (B.boundaryCircle 0) := by
    refine ContinuousMap.ext fun t => Circle.coe_injective ?_
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
      B.coe_boundaryRetraction_boundaryCircle]
    rfl
  rw [h1, circleDegree_comp, circleDegree_circleRotate, mul_one, h2]
  exact B.circleDegree_retraction_outer _ hj rfl hc

theorem circleHom_pantsOuter (ρ : C(PantsPlane, Circle)) :
    circleHom ρ pantsBase.1 (FundamentalGroup.map pantsOuter 1
        (FundamentalGroup.fromPath ⟦circleLoop⟧)) =
      circleHom (ρ.comp (subsetToAmbient pantsRight)) _
          (FundamentalGroup.fromPath ⟦pantsLoopRight⟧) *
        circleHom (ρ.comp (subsetToAmbient pantsLeft)) _
          (FundamentalGroup.fromPath ⟦pantsLoopLeft⟧) := by
  rw [pantsOuter_map_circleLoop, map_mul, ← map_pantsLoopLeft, ← map_pantsLoopRight]
  exact congrArg₂ (· * ·)
    (circleHom_map ρ (subsetToAmbient pantsRight) (interToRight pantsLeft pantsRight pantsBase)
      (FundamentalGroup.fromPath ⟦pantsLoopRight⟧))
    (circleHom_map ρ (subsetToAmbient pantsLeft) (interToLeft pantsLeft pantsRight pantsBase)
      (FundamentalGroup.fromPath ⟦pantsLoopLeft⟧))

theorem toAdd_circleHom_pantsOuter (ρ : C(PantsPlane, Circle)) :
    toAdd (circleHom ρ pantsBase.1 (FundamentalGroup.map pantsOuter 1
        (FundamentalGroup.fromPath ⟦circleLoop⟧))) = circleDegree (ρ.comp pantsOuter) := by
  rw [← markedMap_refl, circleHom_markedMap, circleInt_circleLoop, toAdd_ofAdd, mul_one]

theorem pantsHom_outer_map (B : PlanarBase.{u} 3) (u v : G)
    (κ : FundamentalGroup PantsPlane pantsBase.1 →* G)
    (hL : κ.comp (FundamentalGroup.map (subsetToAmbient pantsLeft)
      (interToLeft pantsLeft pantsRight pantsBase)) = pantsLeftHom v)
    (hR : κ.comp (FundamentalGroup.map (subsetToAmbient pantsRight)
      (interToRight pantsLeft pantsRight pantsBase)) = pantsRightHom u)
    (a : FundamentalGroup Circle 1) :
    κ (FundamentalGroup.map pantsOuter 1 a) =
      (v * u)⁻¹ ^ toAdd (fundamentalGroupCircleEquivInt a) := by
  have hR' : toAdd (circleHom (pantsRetractionRight.comp (subsetToAmbient pantsRight)) _
      (FundamentalGroup.fromPath ⟦pantsLoopRight⟧)) = -1 := by
    have h := toAdd_circleHom_pantsOuter pantsRetractionRight
    have hd : circleDegree (pantsRetractionRight.comp pantsOuter) = -1 :=
      circleDegree_pantsRetraction_pantsOuter B 1 (by decide) (by norm_num [planarCenter])
    rw [circleHom_pantsOuter, circleHom_pantsRetractionRight_left, mul_one, hd] at h
    exact h
  have hL' : toAdd (circleHom (pantsRetractionLeft.comp (subsetToAmbient pantsLeft)) _
      (FundamentalGroup.fromPath ⟦pantsLoopLeft⟧)) = -1 := by
    have h := toAdd_circleHom_pantsOuter pantsRetractionLeft
    have hd : circleDegree (pantsRetractionLeft.comp pantsOuter) = -1 :=
      circleDegree_pantsRetraction_pantsOuter B 2 (by decide) (by norm_num [planarCenter])
    rw [circleHom_pantsOuter, circleHom_pantsRetractionLeft_right, one_mul, hd] at h
    exact h
  have hκL : κ (FundamentalGroup.fromPath ⟦pantsLeftPath.trans pantsMidPath⟧) = v⁻¹ := by
    rw [← map_pantsLoopLeft]
    have h := DFunLike.congr_fun hL (FundamentalGroup.fromPath ⟦pantsLoopLeft⟧)
    refine h.trans ?_
    rw [pantsLeftHom, MonoidHom.comp_apply, zpowersHom_apply, hL', zpow_neg_one]
  have hκR : κ (FundamentalGroup.fromPath ⟦pantsMidPath.symm.trans pantsRightPath⟧) = u⁻¹ := by
    rw [← map_pantsLoopRight]
    have h := DFunLike.congr_fun hR (FundamentalGroup.fromPath ⟦pantsLoopRight⟧)
    refine h.trans ?_
    rw [pantsRightHom, MonoidHom.comp_apply, zpowersHom_apply, hR', zpow_neg_one]
  have hgen : κ (FundamentalGroup.map pantsOuter 1 (FundamentalGroup.fromPath ⟦circleLoop⟧)) =
      (v * u)⁻¹ := by
    rw [pantsOuter_map_circleLoop, map_mul, hκR, hκL, mul_inv_rev]
  conv_lhs => rw [eq_circleLoop_zpow a]
  rw [map_zpow, map_zpow, hgen]

theorem pantsHom_outer (B : PlanarBase.{u} 3) (u v : G)
    (κ : FundamentalGroup PantsPlane pantsBase.1 →* G)
    (hL : κ.comp (FundamentalGroup.map (subsetToAmbient pantsLeft)
      (interToLeft pantsLeft pantsRight pantsBase)) = pantsLeftHom v)
    (hR : κ.comp (FundamentalGroup.map (subsetToAmbient pantsRight)
      (interToRight pantsLeft pantsRight pantsBase)) = pantsRightHom u) :
    ∀ δ : Path pantsBase.1 (pantsCircle 0 1), ∃ k : G, ∀ a,
      κ (GC.Topology.markedMap (pantsCircle 0) 1 δ a) =
        k * (v * u)⁻¹ ^ toAdd (fundamentalGroupCircleEquivInt a) * k⁻¹ := by
  have hc : pantsOuter.comp (circleRotate pantsQuarter⁻¹) = pantsCircle 0 := by
    refine ContinuousMap.ext fun t => ?_
    change pantsCircle 0 (pantsQuarter * (pantsQuarter⁻¹ * t)) = _
    rw [mul_inv_cancel_left]
  rw [← hc]
  refine forall_conj_of_exists κ _ 1 _ ⟨(Path.refl _).trans
    ((PathConnectedSpace.somePath 1 (circleRotate pantsQuarter⁻¹ 1)).map
      pantsOuter.continuous), 1, fun a => ?_⟩
  rw [← markedMap_comp_markedMap, MonoidHom.comp_apply, markedMap_refl,
    pantsHom_outer_map B u v κ hL hR, circleInt_markedMap, circleDegree_circleRotate, one_mul]
  group

end PantsKappa

namespace PlanarBase

theorem exists_pantsHom (B : PlanarBase.{u} 3) {G : Type*} [Group G] (u v : G) :
    ∃ (b₀ : B.surface.Carrier) (κ : FundamentalGroup B.surface.Carrier b₀ →* G),
      ∀ (j : Fin 3) (β : Path b₀ (B.boundaryCircle j 1)), ∃ k : G,
        ∀ a : FundamentalGroup Circle 1,
          κ (GC.Topology.markedMap (B.boundaryCircle j) 1 β a) =
            k * ![(v * u)⁻¹, u, v] j ^ toAdd (fundamentalGroupCircleEquivInt a) * k⁻¹ := by
  obtain ⟨κ, hL, hR⟩ := exists_pantsPlaneHom u v
  let e : C(B.surface.Carrier, PantsPlane) :=
    ⟨fun x => ⟨B.embedding x, planarModel_subset_pantsPlane (B.embedding_mem x)⟩,
      B.isSmoothEmbedding.isEmbedding.continuous.subtype_mk _⟩
  have he : ∀ j, e.comp (B.boundaryCircle j) = pantsCircle j := fun j =>
    ContinuousMap.ext fun t => Subtype.ext (B.embedding_collar j t)
  have hX : ∀ j : Fin 3, ∀ δ : Path pantsBase.1 (pantsCircle j 1), ∃ k : G, ∀ a,
      κ (GC.Topology.markedMap (pantsCircle j) 1 δ a) =
        k * ![(v * u)⁻¹, u, v] j ^ toAdd (fundamentalGroupCircleEquivInt a) * k⁻¹ := by
    intro j
    fin_cases j
    · exact pantsHom_outer B u v κ hL hR
    · exact pantsHom_hole_right u κ hR
    · exact pantsHom_hole_left v κ hL
  refine ⟨B.boundaryCircle 0 1,
    κ.comp (GC.Topology.markedMap e _ (PathConnectedSpace.somePath pantsBase.1 _)),
    fun j β => ?_⟩
  have h := hX j
  rw [← he j] at h
  exact forall_conj_comp κ e _ _ (B.boundaryCircle j) 1 _ h β

end PlanarBase

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W)

theorem injOn_cutMap_of_ne (hLR : ∀ k, G.leftPiece k ≠ G.rightPiece k)
    (i : Fin G.components.count) :
    InjOn G.cutMap (G.components.piece i : Set G.cutCarrier.Carrier) := by
  intro x hx y hy hxy
  rcases Quotient.exact (G.reconstruction.injective hxy) with h | ⟨k, hk, rfl⟩
  · exact h
  · exact (G.flip_notMem_piece k (hLR k) hk hx hy).elim

theorem isPathConnected_pieceImage (i : Fin G.components.count) :
    IsPathConnected (G.pieceImage i) := by
  have := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := G.cutCarrier.Carrier)
    G.cutCarrier.model
  have hc : IsConnected (G.components.piece i : Set G.cutCarrier.Carrier) :=
    isConnected_iff_connectedSpace.mpr (G.components.connected i)
  exact ((G.components.piece i).isOpen.isConnected_iff_isPathConnected.mp hc).image
    G.continuous_cutMap

theorem mem_pieceImage_or_mem_pieceComplImage (i : Fin G.components.count) (w : W.Carrier) :
    w ∈ G.pieceImage i ∨ w ∈ G.pieceComplImage i := by
  obtain ⟨x, rfl⟩ := G.surjective_cutMap w
  by_cases hx : x ∈ G.components.piece i
  · exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr ⟨x, hx, rfl⟩

theorem exists_mem_pieceImage (w : W.Carrier) : ∃ i, w ∈ G.pieceImage i := by
  obtain ⟨x, rfl⟩ := G.surjective_cutMap w
  obtain ⟨i, hi⟩ := mem_iUnion.1 (G.components.covers.symm ▸ mem_univ x)
  exact ⟨i, x, hi, rfl⟩

variable (j : Fin G.pairing.count)

theorem seamSurface_subset_pieceImage_left : G.seamSurface j ⊆ G.pieceImage (G.leftPiece j) := by
  rintro w ⟨t, rfl⟩
  exact ⟨_, G.left_owned j (G.pairing.leftParam j t).2, (G.seamTorus_eq_cutMap j t).symm⟩

theorem seamSurface_subset_pieceImage_right :
    G.seamSurface j ⊆ G.pieceImage (G.rightPiece j) := by
  rintro w ⟨t, rfl⟩
  exact ⟨_, G.right_owned j (G.pairing.rightParam j _).2, (G.seamTorus_eq_cutMap_right j t).symm⟩

section Owned

variable {j}
variable (hS : G.pieceImage (G.leftPiece j) ∩ G.pieceComplImage (G.leftPiece j) ⊆
  G.seamSurface j)
include hS

theorem leftSide_subset_pieceImage_of_inter : G.leftSide j ⊆ G.pieceImage (G.leftPiece j) :=
  G.pathComponentIn_subset_pieceImage_of_inter j hS (G.leftPoint_mem_pieceImage j)
    (G.leftPoint_mem_compl j)

theorem leftRegion_inter_pieceComplImage_subset :
    G.leftRegion j ∩ G.pieceComplImage (G.leftPiece j) ⊆ G.seamCollar j := fun w hw =>
  (hw.1.elim (fun h => G.seamSurface_subset_seamCollar j
    (hS ⟨G.leftSide_subset_pieceImage_of_inter hS h, hw.2⟩)) id : w ∈ G.seamCollar j)

theorem pieceImage_subset_rightRegion_of_inter [ConnectedSpace W.Carrier]
    {i : Fin G.components.count} (hi : G.leftPiece j ≠ i) :
    G.pieceImage i ⊆ G.rightRegion j := by
  intro w hw
  by_cases hw' : w ∈ G.seamSurface j
  · exact Or.inr (G.seamSurface_subset_seamCollar j hw')
  · rcases G.mem_leftSide_or_mem_rightSide j hw' with h | h
    · exact (hw' (hS ⟨G.leftSide_subset_pieceImage_of_inter hS h,
        G.pieceImage_subset_pieceComplImage hi hw⟩)).elim
    · exact Or.inl h

theorem pieceImage_subset_leftRegion_of_inter [ConnectedSpace W.Carrier]
    (hLR : G.leftPiece j ≠ G.rightPiece j) :
    G.pieceImage (G.leftPiece j) ⊆ G.leftRegion j := by
  intro w hw
  by_cases hw' : w ∈ G.seamSurface j
  · exact Or.inr (G.seamSurface_subset_seamCollar j hw')
  · rcases G.mem_leftSide_or_mem_rightSide j hw' with h | h
    · exact Or.inl h
    · exfalso
      have hsub := G.pathComponentIn_subset_pieceImage_of_inter j hS hw hw'
      have hr : G.rightPoint j ∈ pathComponentIn (G.seamSurface j)ᶜ w := by
        rw [pathComponentIn_congr h]
        exact mem_pathComponentIn_self (G.rightPoint_mem_compl j)
      exact G.rightPoint_mem_compl j (hS ⟨hsub hr,
        G.pieceImage_subset_pieceComplImage hLR (G.rightPoint_mem_pieceImage j)⟩)

end Owned

theorem seamCollar_subset_rightRegion [ConnectedSpace W.Carrier] {j' : Fin G.pairing.count}
    (hj : j ≠ j') {i : Fin G.components.count} (hi : G.seamSurface j' ⊆ G.pieceImage i)
    (hiR : G.pieceImage i ⊆ G.rightRegion j) : G.seamCollar j' ⊆ G.rightRegion j := by
  have hdisj := G.seam_disjoint hj
  have hp : G.seamTorus j' torusBase ∈ G.rightSide j := by
    rcases hiR (hi ⟨torusBase, rfl⟩) with h | h
    · exact h
    · exact (Set.disjoint_left.mp hdisj h (G.seamTorus_mem_seamCollar j' torusBase)).elim
  have hsub : G.seamCollar j' ⊆ (G.seamSurface j)ᶜ := fun w hw hw' =>
    Set.disjoint_left.mp hdisj (G.seamSurface_subset_seamCollar j hw') hw
  intro w hw
  left
  have h := (G.isPathConnected_seamCollar j').subset_pathComponentIn
    (G.seamTorus_mem_seamCollar j' torusBase) hsub hw
  change w ∈ pathComponentIn (G.seamSurface j)ᶜ (G.rightPoint j)
  rwa [← pathComponentIn_congr hp]

theorem exists_pieceRetraction (i : Fin G.components.count)
    (hinj : InjOn G.cutMap (G.components.piece i : Set G.cutCarrier.Carrier)) {U : Set W.Carrier}
    (ρ : C(U, W.Carrier)) (hρ : ∀ u, ρ u ∈ G.pieceImage i)
    (hρx : ∀ (x : G.components.piece i) (hx : G.cutMap x ∈ U), ρ ⟨G.cutMap x, hx⟩ = G.cutMap x) :
    ∃ f : C(U, G.components.piece i), ∀ (u : U) (x : G.components.piece i),
      u.1 = G.cutMap x → f u = x := by
  have : CompactSpace (G.components.piece i) :=
    isCompact_iff_compactSpace.mp (G.components.piece_compact i)
  let c : C(G.components.piece i, W.Carrier) := G.pieceToCarrier i
  have hcinj : Function.Injective c := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hemb : Topology.IsEmbedding c := (c.continuous.isClosedEmbedding hcinj).isEmbedding
  have hr : ∀ u, ρ u ∈ range c := fun u => by
    obtain ⟨x, hx, h⟩ := hρ u
    exact ⟨⟨x, hx⟩, h⟩
  let e := hemb.toHomeomorph
  refine ⟨⟨fun u => e.symm ⟨ρ u, hr u⟩, e.symm.continuous.comp (ρ.continuous.subtype_mk _)⟩,
    fun u x hux => ?_⟩
  obtain ⟨w, hx⟩ := u
  change w = G.cutMap x at hux
  subst hux
  change e.symm ⟨ρ ⟨G.cutMap x, hx⟩, hr _⟩ = x
  have h : (⟨ρ ⟨G.cutMap x, hx⟩, hr _⟩ : range c) = ⟨c x, mem_range_self x⟩ :=
    Subtype.ext (hρx x hx)
  rw [h]
  exact hemb.toHomeomorph_symm_apply x

theorem exists_collarShrink_ite {U : Set W.Carrier} {A B : Set W.Carrier} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : ∀ w, w ∈ A ∨ w ∈ B) (hABS : A ∩ B ⊆ G.seamSurface j)
    (hUA : U ∩ A ⊆ G.seamCollar j) (g : C(U, W.Carrier))
    (hg : ∀ u : U, u.1 ∈ G.seamSurface j → g u = u.1) :
    ∃ φ : C(U, W.Carrier), (∀ u : U, u.1 ∈ A → φ u = G.collarShrink j (1, u.1)) ∧
      ∀ u : U, u.1 ∈ B → φ u = g u := by
  classical
  have hshrink : ContinuousOn (fun u : U => G.collarShrink j (1, u.1)) {u | u.1 ∈ A} :=
    (G.continuousOn_collarShrink j).comp (continuous_const.prodMk
      continuous_subtype_val).continuousOn fun u hu => ⟨trivial, hUA ⟨u.2, hu⟩⟩
  have heq : ∀ u : U, u.1 ∈ A → u.1 ∈ B → g u = G.collarShrink j (1, u.1) := fun u hA hB =>
    (hg u (hABS ⟨hA, hB⟩)).trans (G.collarShrink_of_mem_seamSurface j 1 (hABS ⟨hA, hB⟩)).symm
  let φ : U → W.Carrier := fun u => if u.1 ∈ B then g u else G.collarShrink j (1, u.1)
  have hφA : ∀ u : U, u.1 ∈ A → φ u = G.collarShrink j (1, u.1) := by
    intro u hu
    by_cases hb : u.1 ∈ B
    · simp only [φ, hb, ↓reduceIte]
      exact heq u hu hb
    · simp only [φ, hb, ↓reduceIte]
  have hφB : ∀ u : U, u.1 ∈ B → φ u = g u := fun u hu => by simp only [φ, hu, ↓reduceIte]
  have hcont : Continuous φ := by
    have hA' : IsClosed {u : U | u.1 ∈ A} := hA.preimage continuous_subtype_val
    have hB' : IsClosed {u : U | u.1 ∈ B} := hB.preimage continuous_subtype_val
    have hcov : {u : U | u.1 ∈ A} ∪ {u : U | u.1 ∈ B} = univ :=
      eq_univ_of_forall fun u => hAB u.1
    rw [← continuousOn_univ, ← hcov]
    exact ContinuousOn.union_of_isClosed (hshrink.congr fun u hu => hφA u hu)
      (g.continuous.continuousOn.congr fun u hu => hφB u hu) hA' hB'
  exact ⟨⟨φ, hcont⟩, hφA, hφB⟩

end TorusPresentation

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem ownedSide_solid (B : SeifertBlock W d) (m : Fin d.fillingCount)
    (s : B.presentation.OwnedSide (B.presentation.leftPiece (B.seam m))) :
    s.val = .inl (B.seam m) := by
  have hsub := (B.solid m).subsingleton_ownedSide
  have h := congrArg Subtype.val (Subsingleton.elim
    (⟨s.val, s.property.trans (B.leftPiece_seam m)⟩ : B.presentation.OwnedSide _)
    ((B.solid m).port 0))
  rw [B.solid_port] at h
  exact h

theorem leftPiece_ne_rightPiece (B : SeifertBlock W d) (k : Fin B.presentation.pairing.count) :
    B.presentation.leftPiece k ≠ B.presentation.rightPiece k := by
  obtain ⟨m, rfl⟩ := B.seam.surjective k
  rw [B.leftPiece_seam, B.rightPiece_seam]
  exact fun h => Option.some_ne_none _ (B.piece.injective h)

theorem pieceImage_inter_solid (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.pieceImage (B.presentation.leftPiece (B.seam m)) ∩
        B.presentation.pieceComplImage (B.presentation.leftPiece (B.seam m)) ⊆
      B.presentation.seamSurface (B.seam m) :=
  B.presentation.pieceImage_inter_pieceComplImage_subset_of_owned (B.seam m) _
    (B.ownedSide_solid m)

theorem piece_some_ne_none (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.piece (some m) ≠ B.piece none :=
  fun h => Option.some_ne_none _ (B.piece.injective h)

theorem piece_some_ne_some (B : SeifertBlock W d) {m m' : Fin d.fillingCount} (h : m ≠ m') :
    B.piece (some m) ≠ B.piece (some m') :=
  fun h' => h (Option.some_injective _ (B.piece.injective h'))

theorem pieceImage_solid_subset_leftRegion (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.pieceImage (B.piece (some m)) ⊆ B.presentation.leftRegion (B.seam m) := by
  have := B.connectedSpace
  have h := B.presentation.pieceImage_subset_leftRegion_of_inter (B.pieceImage_inter_solid m)
    (B.leftPiece_ne_rightPiece _)
  rwa [B.leftPiece_seam] at h

theorem pieceImage_subset_rightRegion (B : SeifertBlock W d) (m : Fin d.fillingCount)
    {i : Fin B.presentation.components.count} (hi : B.piece (some m) ≠ i) :
    B.presentation.pieceImage i ⊆ B.presentation.rightRegion (B.seam m) := by
  have := B.connectedSpace
  refine B.presentation.pieceImage_subset_rightRegion_of_inter (B.pieceImage_inter_solid m) ?_
  rwa [B.leftPiece_seam]

theorem leftSide_subset_pieceImage (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.leftSide (B.seam m) ⊆ B.presentation.pieceImage (B.piece (some m)) := by
  have h := B.presentation.leftSide_subset_pieceImage_of_inter (B.pieceImage_inter_solid m)
  rwa [B.leftPiece_seam] at h

theorem seamSurface_subset_pieceImage_none (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.seamSurface (B.seam m) ⊆ B.presentation.pieceImage (B.piece none) := by
  have h := B.presentation.seamSurface_subset_pieceImage_right (B.seam m)
  rwa [B.rightPiece_seam] at h

theorem seamSurface_subset_pieceImage_some (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.seamSurface (B.seam m) ⊆ B.presentation.pieceImage (B.piece (some m)) := by
  have h := B.presentation.seamSurface_subset_pieceImage_left (B.seam m)
  rwa [B.leftPiece_seam] at h

theorem seamCollar_subset_rightRegion (B : SeifertBlock W d) {m m' : Fin d.fillingCount}
    (h : m ≠ m') :
    B.presentation.seamCollar (B.seam m') ⊆ B.presentation.rightRegion (B.seam m) := by
  have := B.connectedSpace
  exact B.presentation.seamCollar_subset_rightRegion (B.seam m)
    (fun h' => h (B.seam.injective h')) (B.seamSurface_subset_pieceImage_none m')
    (B.pieceImage_subset_rightRegion m (B.piece_some_ne_none m))

theorem leftRegion_subset_rightRegion (B : SeifertBlock W d) {m m' : Fin d.fillingCount}
    (h : m ≠ m') :
    B.presentation.leftRegion (B.seam m') ⊆ B.presentation.rightRegion (B.seam m) := by
  rintro w (hw | hw)
  · exact B.pieceImage_subset_rightRegion m (B.piece_some_ne_some h)
      (B.leftSide_subset_pieceImage m' hw)
  · exact B.seamCollar_subset_rightRegion h hw

theorem rightRegion_inter_pieceImage_subset (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    B.presentation.rightRegion (B.seam m) ∩ B.presentation.pieceImage (B.piece (some m)) ⊆
      B.presentation.seamCollar (B.seam m) := by
  intro w hw
  rw [← B.presentation.leftRegion_inter_rightRegion (B.seam m) (B.isSeparating_seam m)]
  exact ⟨B.pieceImage_solid_subset_leftRegion m hw.2, hw.1⟩

theorem mem_pieceImage_cases (B : SeifertBlock W d) {m m' : Fin d.fillingCount}
    (hcov : ∀ n, n = m ∨ n = m') (w : W.Carrier) :
    w ∈ B.presentation.pieceImage (B.piece none) ∨
      w ∈ B.presentation.pieceImage (B.piece (some m)) ∨
        w ∈ B.presentation.pieceImage (B.piece (some m')) := by
  obtain ⟨i, hi⟩ := B.presentation.exists_mem_pieceImage w
  rw [← B.piece.apply_symm_apply i] at hi
  rcases h : B.piece.symm i with _ | n
  · rw [h] at hi
    exact Or.inl hi
  · rw [h] at hi
    rcases hcov n with rfl | rfl
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)

theorem exists_leafRetraction (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    ∃ f : C(B.presentation.leftRegion (B.seam m),
        B.presentation.components.piece (B.piece (some m))),
      ∀ t, f (B.presentation.seamTorusToLeft (B.seam m) t) = (B.solid m).portMap 0 t := by
  have hS := B.pieceImage_inter_solid m
  have hU := B.presentation.leftRegion_inter_pieceComplImage_subset hS
  rw [B.leftPiece_seam] at hS hU
  obtain ⟨φ, hφA, hφB⟩ := B.presentation.exists_collarShrink_ite (B.seam m)
    (B.presentation.isClosed_pieceComplImage _) (B.presentation.isClosed_pieceImage _)
    (fun w => (B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) w).symm)
    (fun w hw => hS ⟨hw.2, hw.1⟩) hU ⟨Subtype.val, continuous_subtype_val⟩ (fun u _ => rfl)
  have hφ : ∀ u, φ u ∈ B.presentation.pieceImage (B.piece (some m)) := by
    intro u
    rcases B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) u.1 with h | h
    · rw [hφB u h]
      exact h
    · rw [hφA u h]
      exact B.seamSurface_subset_pieceImage_some m
        (B.presentation.collarShrink_one_mem_seamSurface _ _)
  obtain ⟨f, hf⟩ := B.presentation.exists_pieceRetraction (B.piece (some m))
    (B.presentation.injOn_cutMap_of_ne B.leftPiece_ne_rightPiece _) φ hφ
    (fun x hx => hφB _ ⟨x, x.2, rfl⟩)
  refine ⟨f, fun t => ?_⟩
  have hmem : (B.presentation.pairing.leftParam (B.seam m) t : B.presentation.cutCarrier.Carrier) ∈
      B.presentation.components.piece (B.piece (some m)) := by
    rw [← B.leftPiece_seam]
    exact B.presentation.left_owned _ (B.presentation.pairing.leftParam _ t).2
  rw [hf _ ⟨_, hmem⟩ (B.presentation.seamTorus_eq_cutMap (B.seam m) t)]
  apply Subtype.ext
  rw [ProductFibredPiece.portMap_val, B.solid_port]
  exact (B.presentation.pairing.left_zero _ t).symm

end SeifertBlock

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem portMap_filled_val (B : SeifertBlock W d) (n : Fin d.fillingCount) (x : Torus) :
    (B.product.portMap (B.port (.inr n)) x : B.presentation.cutCarrier.Carrier) =
      B.presentation.pairing.rightParam (B.seam n) x := by
  rw [ProductFibredPiece.portMap_val, B.filled_port]
  exact B.presentation.pairing.right_zero _ x

theorem portMap_solid_val (B : SeifertBlock W d) (n : Fin d.fillingCount) (x : Torus) :
    ((B.solid n).portMap 0 x : B.presentation.cutCarrier.Carrier) =
      B.presentation.pairing.leftParam (B.seam n) x := by
  rw [ProductFibredPiece.portMap_val, B.solid_port]
  exact B.presentation.pairing.left_zero _ x

theorem middle_seam (B : SeifertBlock W d) {U : Set W.Carrier}
    (f : C(U, B.presentation.components.piece (B.piece none)))
    (hf : ∀ (u : U) (x : B.presentation.components.piece (B.piece none)),
      u.1 = B.presentation.cutMap x → f u = x)
    (n : Fin d.fillingCount) (t : Torus) (hu : B.presentation.seamTorus (B.seam n) t ∈ U) :
    f ⟨_, hu⟩ = B.product.portMap (B.port (.inr n))
      (B.presentation.pairing.matching (B.seam n) t) := by
  refine hf _ _ ?_
  change B.presentation.seamTorus (B.seam n) t = _
  rw [B.presentation.seamTorus_eq_cutMap_right, B.portMap_filled_val]

theorem isPathConnected_middle (B : SeifertBlock W d) {m m' : Fin d.fillingCount}
    (hmm : m ≠ m') (hcov : ∀ n, n = m ∨ n = m') :
    IsPathConnected (B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m')) := by
  have := B.connectedSpace
  have hP : B.presentation.pieceImage (B.piece none) ⊆ B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m') := fun w hw =>
    ⟨B.pieceImage_subset_rightRegion m (B.piece_some_ne_none m) hw,
      B.pieceImage_subset_rightRegion m' (B.piece_some_ne_none m') hw⟩
  have hC : B.presentation.seamCollar (B.seam m) ⊆ B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m') := fun w hw =>
    ⟨Or.inr hw, B.seamCollar_subset_rightRegion (Ne.symm hmm) hw⟩
  have hC' : B.presentation.seamCollar (B.seam m') ⊆ B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m') := fun w hw =>
    ⟨B.seamCollar_subset_rightRegion hmm hw, Or.inr hw⟩
  have heq : B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m') =
      B.presentation.pieceImage (B.piece none) ∪ B.presentation.seamCollar (B.seam m) ∪
        B.presentation.seamCollar (B.seam m') := by
    refine Subset.antisymm (fun w hw => ?_) (union_subset (union_subset hP hC) hC')
    rcases B.mem_pieceImage_cases hcov w with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (B.rightRegion_inter_pieceImage_subset m ⟨hw.1, h⟩))
    · exact Or.inr (B.rightRegion_inter_pieceImage_subset m' ⟨hw.2, h⟩)
  rw [heq]
  exact ((B.presentation.isPathConnected_pieceImage _).union
    (B.presentation.isPathConnected_seamCollar _)
    ⟨_, B.seamSurface_subset_pieceImage_none m ⟨torusBase, rfl⟩,
      B.presentation.seamTorus_mem_seamCollar _ torusBase⟩).union
    (B.presentation.isPathConnected_seamCollar _)
    ⟨_, Or.inl (B.seamSurface_subset_pieceImage_none m' ⟨torusBase, rfl⟩),
      B.presentation.seamTorus_mem_seamCollar _ torusBase⟩

theorem exists_middleRetraction (B : SeifertBlock W d) {m m' : Fin d.fillingCount}
    (hmm : m ≠ m') (hcov : ∀ n, n = m ∨ n = m') :
    ∃ f : C(↥(B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m')),
        B.presentation.components.piece (B.piece none)),
      ∀ (u : ↥(B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m')))
        (x : B.presentation.components.piece (B.piece none)),
        u.1 = B.presentation.cutMap x → f u = x := by
  have hS := B.pieceImage_inter_solid m
  have hS' := B.pieceImage_inter_solid m'
  rw [B.leftPiece_seam] at hS hS'
  obtain ⟨φ₁, h1A, h1B⟩ := B.presentation.exists_collarShrink_ite (B.seam m')
    (U := B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m'))
    (B.presentation.isClosed_pieceImage _) (B.presentation.isClosed_pieceComplImage _)
    (B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m'))) hS'
    (fun w hw => B.rightRegion_inter_pieceImage_subset m' ⟨hw.1.2, hw.2⟩)
    ⟨Subtype.val, continuous_subtype_val⟩ (fun u _ => rfl)
  obtain ⟨φ₂, h2A, h2B⟩ := B.presentation.exists_collarShrink_ite (B.seam m)
    (U := B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m'))
    (B.presentation.isClosed_pieceImage _) (B.presentation.isClosed_pieceComplImage _)
    (B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m))) hS
    (fun w hw => B.rightRegion_inter_pieceImage_subset m ⟨hw.1.1, hw.2⟩) φ₁
    (fun u hu => h1B u (B.presentation.pieceImage_subset_pieceComplImage
      (B.piece_some_ne_some (Ne.symm hmm)) (B.seamSurface_subset_pieceImage_some m hu)))
  have hP : ∀ u : ↥(B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m')),
      u.1 ∈ B.presentation.pieceImage (B.piece none) → φ₂ u = u.1 := fun u hu =>
    (h2B u (B.presentation.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m) hu)).trans
      (h1B u (B.presentation.pieceImage_subset_pieceComplImage (B.piece_some_ne_none m') hu))
  have hφ : ∀ u, φ₂ u ∈ B.presentation.pieceImage (B.piece none) := by
    intro u
    rcases B.mem_pieceImage_cases hcov u.1 with h | h | h
    · rw [hP u h]
      exact h
    · rw [h2A u h]
      exact B.seamSurface_subset_pieceImage_none m
        (B.presentation.collarShrink_one_mem_seamSurface _ _)
    · rcases B.presentation.mem_pieceImage_or_mem_pieceComplImage (B.piece (some m)) u.1
        with h' | h'
      · rw [h2A u h']
        exact B.seamSurface_subset_pieceImage_none m
          (B.presentation.collarShrink_one_mem_seamSurface _ _)
      · rw [h2B u h', h1A u h]
        exact B.seamSurface_subset_pieceImage_none m'
          (B.presentation.collarShrink_one_mem_seamSurface _ _)
  exact B.presentation.exists_pieceRetraction (B.piece none)
    (B.presentation.injOn_cutMap_of_ne B.leftPiece_ne_rightPiece _) φ₂ hφ
    (fun x hx => hP ⟨_, hx⟩ ⟨x, x.2, rfl⟩)

end SeifertBlock

section CircleMarked
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem circleInt_markedMap_eq (f : C(X, Circle)) (x : X) (δ δ' : Path 1 (f x))
    (a : FundamentalGroup X x) :
    fundamentalGroupCircleEquivInt (GC.Topology.markedMap f x δ a) =
      fundamentalGroupCircleEquivInt (GC.Topology.markedMap f x δ' a) := by
  obtain ⟨k, hk⟩ := exists_conj_markedMap fundamentalGroupCircleEquivInt.toMonoidHom f x δ δ'
  have h := hk a
  simp only [MulEquiv.coe_toMonoidHom] at h
  rw [h, mul_comm k, mul_inv_cancel_right]

theorem circleHom_markedMap_eq (ρ : C(Y, Circle)) (f : C(X, Y)) (x : X) {y : Y}
    (δ : Path y (f x)) (a : FundamentalGroup X x) :
    circleHom ρ y (GC.Topology.markedMap f x δ a) = circleHom (ρ.comp f) x a := by
  simp only [circleHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← MonoidHom.comp_apply (GC.Topology.markedMap ρ y _), markedMap_comp_markedMap]
  exact circleInt_markedMap_eq _ x _ _ a

theorem circleHom_snd (g : FundamentalGroup Torus torusBase) :
    circleHom ContinuousMap.snd torusBase g = (GC.Topology.torusFundamentalGroup g).2 := by
  rw [circleHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    circleInt_markedMap_eq _ _ _ (Path.refl (ContinuousMap.snd torusBase))]
  exact congrArg fundamentalGroupCircleEquivInt
    (DFunLike.congr_fun (markedMap_refl ContinuousMap.snd torusBase) g)

theorem toAdd_torusCoordinates_zero (g : FundamentalGroup Torus torusBase) :
    toAdd (torusCoordinates g) 0 = toAdd (GC.Topology.torusFundamentalGroup g).1 := by
  rw [toAdd_torusCoordinates]
  rfl

theorem toAdd_torusCoordinates_one (g : FundamentalGroup Torus torusBase) :
    toAdd (torusCoordinates g) 1 = toAdd (GC.Topology.torusFundamentalGroup g).2 := by
  rw [toAdd_torusCoordinates]
  rfl

end CircleMarked

section Conj
variable {X T : Type*} [TopologicalSpace X] [TopologicalSpace T] {G : Type*} [Group G] {x : X}

theorem forall_conj_congr (F : FundamentalGroup X x →* G) {f g : C(T, X)} (hfg : f = g) (t : T)
    (E : FundamentalGroup T t → G)
    (h : ∀ δ : Path x (g t), ∃ k : G, ∀ a,
      F (GC.Topology.markedMap g t δ a) = k * E a * k⁻¹) :
    ∀ δ : Path x (f t), ∃ k : G, ∀ a, F (GC.Topology.markedMap f t δ a) = k * E a * k⁻¹ := by
  subst hfg
  exact h

theorem forall_conj_comp_torus (F : FundamentalGroup X x →* G) (f : C(Torus, X))
    (M : C(Torus, Torus)) (E : FundamentalGroup Torus torusBase → G)
    (h : ∀ δ : Path x (f torusBase), ∃ k : G, ∀ g,
      F (GC.Topology.markedMap f torusBase δ g) = k * E g * k⁻¹) :
    ∀ δ : Path x ((f.comp M) torusBase), ∃ k : G, ∀ g,
      F (GC.Topology.markedMap (f.comp M) torusBase δ g) = k * E (torusAut M g) * k⁻¹ := by
  intro δ
  let γ := PathConnectedSpace.somePath torusBase (M torusBase)
  refine forall_conj_of_exists F (f.comp M) torusBase (fun g => E (torusAut M g))
    ⟨(δ.trans (γ.symm.map f.continuous)).trans (γ.map f.continuous), ?_⟩ δ
  obtain ⟨k, hk⟩ := h (δ.trans (γ.symm.map f.continuous))
  refine ⟨k, fun g => ?_⟩
  rw [← markedMap_comp_markedMap, MonoidHom.comp_apply]
  exact hk _

theorem forall_conj_changeBasepoint {y : X} (F : FundamentalGroup X y →* G) (β : Path y x)
    (f : C(T, X)) (t : T) (E : FundamentalGroup T t → G)
    (h : ∀ δ : Path y (f t), ∃ k : G, ∀ a,
      F (GC.Topology.markedMap f t δ a) = k * E a * k⁻¹) :
    ∀ δ : Path x (f t), ∃ k : G, ∀ a,
      (F.comp (fundamentalGroupChangeBasepoint β).toMonoidHom)
        (GC.Topology.markedMap f t δ a) = k * E a * k⁻¹ := by
  intro δ
  obtain ⟨k, hk⟩ := h (β.trans δ)
  refine ⟨k, fun a => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← markedMap_trans]
  exact hk a

end Conj

theorem exists_hom_glue_solid {Z : Type*} [TopologicalSpace Z] (U V : Set Z) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = univ) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace ↑(U ∩ V)] (τ : C(Torus, ↑(U ∩ V)))
    (hτ : Function.Surjective (FundamentalGroup.map τ torusBase)) (φ : C(U, Circle))
    (hφ : φ.comp ((DifferentialGeometry.Topology.VanKampen.interToLeft U V).comp τ) =
      ContinuousMap.snd)
    {G : Type*} [Group G]
    (fR : FundamentalGroup V
      (DifferentialGeometry.Topology.VanKampen.interToRight U V (τ torusBase)) →* G) (y : G)
    (hfR : ∀ g, fR (FundamentalGroup.map
      ((DifferentialGeometry.Topology.VanKampen.interToRight U V).comp τ) torusBase g) =
        y ^ toAdd (GC.Topology.torusFundamentalGroup g).2) :
    ∃ F : FundamentalGroup Z (τ torusBase).1 →* G,
      F.comp (FundamentalGroup.map (DifferentialGeometry.Topology.VanKampen.subsetToAmbient V)
        (DifferentialGeometry.Topology.VanKampen.interToRight U V (τ torusBase))) = fR := by
  open DifferentialGeometry.Topology.VanKampen in
  let fL : FundamentalGroup U (interToLeft U V (τ torusBase)) →* G :=
    (zpowersHom G y).comp (circleHom φ _)
  open DifferentialGeometry.Topology.VanKampen in
  have hcompat : fL.comp (FundamentalGroup.map (interToLeft U V) (τ torusBase)) =
      fR.comp (FundamentalGroup.map (interToRight U V) (τ torusBase)) := by
    refine MonoidHom.ext fun c => ?_
    obtain ⟨g, rfl⟩ := hτ c
    have h1 := DFunLike.congr_fun
      (GC.Topology.fundamentalGroup_map_comp τ (interToLeft U V) torusBase) g
    have h2 := DFunLike.congr_fun
      (GC.Topology.fundamentalGroup_map_comp τ (interToRight U V) torusBase) g
    simp only [MonoidHom.comp_apply] at h1 h2 ⊢
    rw [← h1, ← h2, hfR]
    simp only [fL, MonoidHom.comp_apply, zpowersHom_apply]
    have key := circleHom_map φ ((interToLeft U V).comp τ) torusBase g
    rw [hφ, circleHom_snd] at key
    exact congrArg (fun z => y ^ toAdd z) key
  obtain ⟨F, -, hF⟩ := exists_hom_of_openCover U V hU hV hcover (τ torusBase) fL fR hcompat
  exact ⟨F, hF⟩

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def fibreMap (P : ProductFibredPiece T i k) : C(T.components.piece i, Circle) :=
  ContinuousMap.snd.comp P.trivializationInv

def baseMap (P : ProductFibredPiece T i k) : C(T.components.piece i, P.base.surface.Carrier) :=
  ContinuousMap.fst.comp P.trivializationInv

theorem fibreMap_comp_portMap (P : ProductFibredPiece T i k) (j : Fin k) :
    P.fibreMap.comp (P.portMap j) = ContinuousMap.snd := by
  refine ContinuousMap.ext fun x => ?_
  change (P.trivialization.symm (P.trivialization (P.base.boundaryCircle j x.1, x.2))).2 = x.2
  rw [Diffeomorph.symm_apply_apply]

theorem baseMap_comp_portMap (P : ProductFibredPiece T i k) (j : Fin k) :
    P.baseMap.comp (P.portMap j) = (P.base.boundaryCircle j).comp ContinuousMap.fst := by
  refine ContinuousMap.ext fun x => ?_
  change (P.trivialization.symm (P.trivialization (P.base.boundaryCircle j x.1, x.2))).1 = _
  rw [Diffeomorph.symm_apply_apply]
  rfl

def productHom (P : ProductFibredPiece T i k) {H : Type*} [Group H]
    {b₀ : P.base.surface.Carrier} (κ : FundamentalGroup P.base.surface.Carrier b₀ →* H)
    (y : T.components.piece i) (β : Path b₀ (P.baseMap y)) :
    FundamentalGroup (T.components.piece i) y →* H × Multiplicative ℤ :=
  MonoidHom.prod (κ.comp (GC.Topology.markedMap P.baseMap y β)) (circleHom P.fibreMap y)

theorem productHom_port (P : ProductFibredPiece T i k) {H : Type*} [Group H]
    {b₀ : P.base.surface.Carrier} (κ : FundamentalGroup P.base.surface.Carrier b₀ →* H)
    (y : T.components.piece i) (β : Path b₀ (P.baseMap y)) (j : Fin k) (w : H)
    (hκ : ∀ γ : Path b₀ (P.base.boundaryCircle j 1), ∃ c : H, ∀ a : FundamentalGroup Circle 1,
      κ (GC.Topology.markedMap (P.base.boundaryCircle j) 1 γ a) =
        c * w ^ toAdd (fundamentalGroupCircleEquivInt a) * c⁻¹) :
    ∀ δ : Path y (P.portMap j torusBase), ∃ c : H × Multiplicative ℤ, ∀ g,
      P.productHom κ y β (GC.Topology.markedMap (P.portMap j) torusBase δ g) =
        c * (w ^ toAdd (GC.Topology.torusFundamentalGroup g).1,
          (GC.Topology.torusFundamentalGroup g).2) * c⁻¹ := by
  intro δ
  have hbase : ∀ δ' : Path b₀ ((P.baseMap.comp (P.portMap j)) torusBase), ∃ c : H, ∀ g,
      κ (GC.Topology.markedMap (P.baseMap.comp (P.portMap j)) torusBase δ' g) =
        c * w ^ toAdd (GC.Topology.torusFundamentalGroup g).1 * c⁻¹ := by
    refine forall_conj_congr κ (P.baseMap_comp_portMap j) torusBase _ fun δ' => ?_
    obtain ⟨c, hc⟩ := hκ δ'
    refine ⟨c, fun g => ?_⟩
    rw [← markedMap_comp_map ContinuousMap.fst (P.base.boundaryCircle j) torusBase δ',
      MonoidHom.comp_apply]
    exact hc _
  obtain ⟨c, hc⟩ := hbase (β.trans (δ.map P.baseMap.continuous))
  refine ⟨(c, 1), fun g => Prod.ext ?_ ?_⟩
  · simp only [productHom, MonoidHom.prod_apply, MonoidHom.comp_apply, Prod.fst_mul,
      Prod.fst_inv]
    rw [← MonoidHom.comp_apply (GC.Topology.markedMap P.baseMap y β), markedMap_comp_markedMap,
      hc]
  · simp only [productHom, MonoidHom.prod_apply, Prod.snd_mul, Prod.snd_inv, one_mul, inv_one,
      mul_one]
    rw [circleHom_markedMap_eq, P.fibreMap_comp_portMap, circleHom_snd]

end ProductFibredPiece

section Relations

def twoFillingIncl (p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ) :
    FreeGroup (Fin 2) × Multiplicative ℤ →* TwoFillingGroup p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ :=
  (Monoid.PushoutI.of (φ := firstFillingEdge p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂) true).comp
    (Monoid.PushoutI.of (φ := secondFillingEdge p₂ q₂ r₂ s₂) true)

theorem twoFillingIncl_first (p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ) :
    twoFillingIncl p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ (FreeGroup.of 0 ^ p₁, ofAdd q₁) = 1 := by
  have h := DFunLike.congr_fun
    (Monoid.PushoutI.of_comp_eq_base (φ := firstFillingEdge p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂) true)
    ((ofAdd 1, 1) : SeamGroup)
  have h' := DFunLike.congr_fun
    (Monoid.PushoutI.of_comp_eq_base (φ := firstFillingEdge p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂) false)
    ((ofAdd 1, 1) : SeamGroup)
  rw [← h'] at h
  simpa [firstFillingEdge, seamLinearForm_apply, twoFillingIncl] using h

theorem twoFillingIncl_second (p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ) :
    twoFillingIncl p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ (FreeGroup.of 1 ^ p₂, ofAdd q₂) = 1 := by
  have h := DFunLike.congr_fun
    (Monoid.PushoutI.of_comp_eq_base (φ := secondFillingEdge p₂ q₂ r₂ s₂) true)
    ((ofAdd 1, 1) : SeamGroup)
  have h' := DFunLike.congr_fun
    (Monoid.PushoutI.of_comp_eq_base (φ := secondFillingEdge p₂ q₂ r₂ s₂) false)
    ((ofAdd 1, 1) : SeamGroup)
  rw [← h'] at h
  have h2 := congrArg (Monoid.PushoutI.of (φ := firstFillingEdge p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂) true) h
  simpa [secondFillingEdge, seamLinearForm_apply, twoFillingIncl] using h2

theorem twoFillingPort_inv (p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ) (v : SeamGroup) :
    twoFillingPort p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ (invMonoidHom.prodMap (MonoidHom.id _) v) =
      twoFillingIncl p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂
        ((FreeGroup.of 0 * FreeGroup.of 1)⁻¹ ^ toAdd v.1, v.2) := by
  change twoFillingIncl p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂
      ((zpowersHom _ (FreeGroup.of 0 * FreeGroup.of 1)) v.1⁻¹, v.2) = _
  rw [zpowersHom_apply, toAdd_inv, zpow_neg, inv_zpow]

theorem incl_relation_of_slope {H : Type*} [Group H]
    (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H) (w : FreeGroup (Fin 2)) {p q x y : ℤ}
    (hpq : ι (w ^ p, ofAdd q) = 1) (hxy : (x, y) = (p, q) ∨ (x, y) = -(p, q)) :
    ι (w ^ x, ofAdd y) = 1 := by
  rcases hxy with h | h
  · simp only [Prod.mk.injEq] at h
    rw [h.1, h.2, hpq]
  · simp only [Prod.neg_mk, Prod.mk.injEq] at h
    have he : ((w ^ x, ofAdd y) : FreeGroup (Fin 2) × Multiplicative ℤ) = (w ^ p, ofAdd q)⁻¹ := by
      rw [h.1, h.2]
      refine Prod.ext ?_ ?_
      · simp [zpow_neg]
      · rfl
    rw [he, map_inv, hpq, inv_one]

theorem seam_value {H : Type*} [Group H] (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H)
    (w : FreeGroup (Fin 2)) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : ι (w ^ M 0 0, ofAdd (M 1 0)) = 1) (c : FreeGroup (Fin 2) × Multiplicative ℤ)
    (v : Fin 2 → ℤ) :
    ι (c * (w ^ (M.mulVec v) 0, ofAdd ((M.mulVec v) 1)) * c⁻¹) =
      (ι c * ι (w ^ M 0 1, ofAdd (M 1 1)) * (ι c)⁻¹) ^ v 1 := by
  have hsplit : ((w ^ (M.mulVec v) 0, ofAdd ((M.mulVec v) 1)) :
      FreeGroup (Fin 2) × Multiplicative ℤ) =
      (w ^ M 0 0, ofAdd (M 1 0)) ^ v 0 * (w ^ M 0 1, ofAdd (M 1 1)) ^ v 1 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    refine Prod.ext ?_ (toAdd.injective ?_)
    · simp only [Prod.fst_mul, Prod.pow_fst, ← zpow_mul, ← zpow_add]
    · simp only [Prod.snd_mul, Prod.pow_snd, toAdd_mul, toAdd_zpow, toAdd_ofAdd, smul_eq_mul]
      ring
  rw [hsplit, map_mul, map_mul, map_mul, map_zpow, map_zpow, hM, one_zpow, one_mul, map_inv,
    conj_zpow]

theorem exists_pants_values (e₀ e₁ ef : Fin 3) (h01 : e₀ ≠ e₁) (hf0 : ef ≠ e₀)
    (hf1 : ef ≠ e₁) :
    ∃ u v k : FreeGroup (Fin 2), ![(v * u)⁻¹, u, v] e₀ = FreeGroup.of 0 ∧
      ![(v * u)⁻¹, u, v] e₁ = FreeGroup.of 1 ∧
        ![(v * u)⁻¹, u, v] ef = k * (FreeGroup.of 0 * FreeGroup.of 1)⁻¹ * k⁻¹ := by
  fin_cases e₀ <;> fin_cases e₁ <;> fin_cases ef <;>
    first
    | exact absurd rfl h01
    | exact absurd rfl hf0
    | exact absurd rfl hf1
    | skip
  · exact ⟨FreeGroup.of 1, (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹, (FreeGroup.of 0)⁻¹,
      by simp, rfl, by simp [mul_assoc]⟩
  · exact ⟨(FreeGroup.of 0 * FreeGroup.of 1)⁻¹, FreeGroup.of 1, 1, by simp, rfl,
      by simp⟩
  · exact ⟨FreeGroup.of 0, (FreeGroup.of 0 * FreeGroup.of 1)⁻¹, 1, rfl, by simp [mul_assoc],
      by simp⟩
  · exact ⟨FreeGroup.of 0, FreeGroup.of 1, (FreeGroup.of 0)⁻¹, rfl, rfl, by simp [mul_assoc]⟩
  · exact ⟨(FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹, FreeGroup.of 0, (FreeGroup.of 0)⁻¹,
      rfl, by simp, by simp [mul_assoc]⟩
  · exact ⟨FreeGroup.of 1, FreeGroup.of 0, 1, rfl, rfl, by simp⟩

end Relations

section ConjTools
variable {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
  {G : Type*} [Group G]

theorem forall_conj_pull (h : C(Y, X)) {y : Y} (F' : FundamentalGroup X (h y) →* G)
    (p : C(T, Y)) (t : T) (E : FundamentalGroup T t → G)
    (H : ∀ δ : Path (h y) ((h.comp p) t), ∃ k : G, ∀ a,
      F' (GC.Topology.markedMap (h.comp p) t δ a) = k * E a * k⁻¹) :
    ∀ δ : Path y (p t), ∃ k : G, ∀ a,
      (F'.comp (FundamentalGroup.map h y)) (GC.Topology.markedMap p t δ a) = k * E a * k⁻¹ := by
  intro δ
  obtain ⟨k, hk⟩ := H (δ.map h.continuous)
  refine ⟨k, fun a => ?_⟩
  rw [MonoidHom.comp_apply, ← MonoidHom.comp_apply (FundamentalGroup.map h y),
    map_comp_markedMap]
  exact hk a

theorem forall_conj_map {H : Type*} [Group H] (ι : G →* H) {x : X}
    (F : FundamentalGroup X x →* G) (f : C(T, X)) (t : T) (E : FundamentalGroup T t → G)
    (h : ∀ δ : Path x (f t), ∃ k : G, ∀ a,
      F (GC.Topology.markedMap f t δ a) = k * E a * k⁻¹) :
    ∀ δ : Path x (f t), ∃ k : H, ∀ a,
      (ι.comp F) (GC.Topology.markedMap f t δ a) = k * ι (E a) * k⁻¹ := by
  intro δ
  obtain ⟨k, hk⟩ := h δ
  refine ⟨ι k, fun a => ?_⟩
  rw [MonoidHom.comp_apply, hk, map_mul, map_mul, map_inv]

end ConjTools

theorem TorusPresentation.pathConnectedSpace_piece {W : CompactCarrier.{u}}
    (G : TorusPresentation W) (i : Fin G.components.count) :
    PathConnectedSpace (G.components.piece i) := by
  have := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := G.cutCarrier.Carrier)
    G.cutCarrier.model
  have hc : IsConnected (G.components.piece i : Set G.cutCarrier.Carrier) :=
    isConnected_iff_connectedSpace.mpr (G.components.connected i)
  exact isPathConnected_iff_pathConnectedSpace.mp
    ((G.components.piece i).isOpen.isConnected_iff_isPathConnected.mp hc)

theorem ProductFibredPiece.pathConnectedSpace_base {W : CompactCarrier.{u}}
    {T : TorusPresentation.{u} W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) : PathConnectedSpace P.base.surface.Carrier := by
  have := T.pathConnectedSpace_piece i
  refine Function.Surjective.pathConnectedSpace (f := P.baseMap) (fun b => ?_) P.baseMap.continuous
  refine ⟨P.trivialization (b, 1), ?_⟩
  change (P.trivialization.symm (P.trivialization (b, 1))).1 = b
  rw [Diffeomorph.symm_apply_apply]

theorem port_matching_value {H : Type*} [Group H] (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H)
    (w : FreeGroup (Fin 2)) (M : C(Torus, Torus))
    (hM : ι (w ^ torusMapMatrix M 0 0, ofAdd (torusMapMatrix M 1 0)) = 1)
    (g : FundamentalGroup Torus torusBase) :
    ι (w ^ toAdd (GC.Topology.torusFundamentalGroup (torusAut M g)).1,
        (GC.Topology.torusFundamentalGroup (torusAut M g)).2) =
      ι (w ^ torusMapMatrix M 0 1, ofAdd (torusMapMatrix M 1 1)) ^
        toAdd (GC.Topology.torusFundamentalGroup g).2 := by
  have hv := torusMapMatrix_mulVec M g
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  rw [toAdd_torusCoordinates_zero] at h0
  rw [toAdd_torusCoordinates_one] at h1
  have key := seam_value ι w (torusMapMatrix M) hM 1 (toAdd (torusCoordinates g))
  rw [one_mul, inv_one, mul_one, map_one, one_mul, inv_one, mul_one, h0,
    toAdd_torusCoordinates_one] at key
  rw [← key, h1]
  rfl

namespace SeifertBlock

open DifferentialGeometry.Topology.VanKampen

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem forall_conj_product (B : SeifertBlock W d) {H : Type*} [Group H]
    (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H) {b₀ : B.product.base.surface.Carrier}
    (κ : FundamentalGroup B.product.base.surface.Carrier b₀ →* FreeGroup (Fin 2))
    {U : Set W.Carrier} (f : C(U, B.presentation.components.piece (B.piece none))) (y : U)
    (β : Path b₀ (B.product.baseMap (f y))) (p : C(Torus, U)) (c : Fin d.k)
    (M : C(Torus, Torus)) (hp : f.comp p = (B.product.portMap c).comp M)
    (w : FreeGroup (Fin 2))
    (hκ : ∀ γ : Path b₀ (B.product.base.boundaryCircle c 1), ∃ c' : FreeGroup (Fin 2), ∀ a,
      κ (GC.Topology.markedMap (B.product.base.boundaryCircle c) 1 γ a) =
        c' * w ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹) :
    ∀ δ : Path y (p torusBase), ∃ k : H, ∀ g,
      ((ι.comp (B.product.productHom κ (f y) β)).comp (FundamentalGroup.map f y))
          (GC.Topology.markedMap p torusBase δ g) =
        k * ι (w ^ toAdd (GC.Topology.torusFundamentalGroup (torusAut M g)).1,
          (GC.Topology.torusFundamentalGroup (torusAut M g)).2) * k⁻¹ := by
  let E : FundamentalGroup Torus torusBase → H := fun g =>
    ι (w ^ toAdd (GC.Topology.torusFundamentalGroup g).1, (GC.Topology.torusFundamentalGroup g).2)
  refine forall_conj_pull f _ p torusBase (fun g => E (torusAut M g)) ?_
  refine forall_conj_congr _ hp torusBase (fun g => E (torusAut M g)) ?_
  refine forall_conj_comp_torus _ _ M E ?_
  intro δ
  obtain ⟨k, hk⟩ := B.product.productHom_port κ (f y) β c w hκ δ
  exact ⟨ι k, fun g => by rw [MonoidHom.comp_apply, hk, map_mul, map_mul, map_inv]⟩

theorem exists_inner_hom (B : SeifertBlock W d) {m m' : Fin d.fillingCount} (hmm : m ≠ m')
    (hcov : ∀ n, n = m ∨ n = m') {H : Type*} [Group H]
    (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H) {b₀ : B.product.base.surface.Carrier}
    (κ : FundamentalGroup B.product.base.surface.Carrier b₀ →* FreeGroup (Fin 2))
    (f : C(↥(B.presentation.rightRegion (B.seam m) ∩ B.presentation.rightRegion (B.seam m')),
      B.presentation.components.piece (B.piece none)))
    (hf : ∀ (u : ↥(B.presentation.rightRegion (B.seam m) ∩
        B.presentation.rightRegion (B.seam m')))
      (x : B.presentation.components.piece (B.piece none)),
        u.1 = B.presentation.cutMap x → f u = x)
    (w' : FreeGroup (Fin 2))
    (hκ' : ∀ γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inr m')) 1),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m'))) 1 γ a) =
          c' * w' ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹)
    (hM' : ι (w' ^ torusMapMatrix (B.presentation.matchingMap (B.seam m')) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m')) 1 0)) = 1) :
    ∃ (z₀ : ↥(B.presentation.rightRegion (B.seam m)))
      (F₀ : FundamentalGroup ↥(B.presentation.rightRegion (B.seam m)) z₀ →* H),
      ∀ (p : C(Torus, ↥(B.presentation.rightRegion (B.seam m) ∩
          B.presentation.rightRegion (B.seam m')))) (c : Fin d.k) (M : C(Torus, Torus)),
        f.comp p = (B.product.portMap c).comp M → ∀ w : FreeGroup (Fin 2),
        (∀ γ : Path b₀ (B.product.base.boundaryCircle c 1), ∃ c' : FreeGroup (Fin 2), ∀ a,
          κ (GC.Topology.markedMap (B.product.base.boundaryCircle c) 1 γ a) =
            c' * w ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹) →
        ∀ δ : Path z₀ (((interToLeft (B.presentation.rightRegion (B.seam m))
            (B.presentation.rightRegion (B.seam m'))).comp p) torusBase), ∃ k : H, ∀ g,
          F₀ (GC.Topology.markedMap ((interToLeft (B.presentation.rightRegion (B.seam m))
              (B.presentation.rightRegion (B.seam m'))).comp p) torusBase δ g) =
            k * ι (w ^ toAdd (GC.Topology.torusFundamentalGroup (torusAut M g)).1,
              (GC.Topology.torusFundamentalGroup (torusAut M g)).2) * k⁻¹ := by
  have := B.connectedSpace
  have hsep' := B.isSeparating_seam m'
  have hLR' := B.leftRegion_subset_rightRegion hmm
  have hCR := B.seamCollar_subset_rightRegion hmm
  have := B.product.pathConnectedSpace_base
  let U' : Set ↥(B.presentation.rightRegion (B.seam m)) :=
    (↑) ⁻¹' B.presentation.leftRegion (B.seam m')
  let V' : Set ↥(B.presentation.rightRegion (B.seam m)) :=
    (↑) ⁻¹' B.presentation.rightRegion (B.seam m')
  have hU' : IsOpen U' :=
    (B.presentation.isOpen_leftRegion (B.seam m')).preimage continuous_subtype_val
  have hV' : IsOpen V' :=
    (B.presentation.isOpen_rightRegion (B.seam m')).preimage continuous_subtype_val
  have hcover' : U' ∪ V' = univ := eq_univ_of_forall fun z => by
    have h := (B.presentation.leftRegion_union_rightRegion (B.seam m')).symm ▸ mem_univ z.1
    exact h
  have : PathConnectedSpace U' := isPathConnected_iff_pathConnectedSpace.mp
    ((B.presentation.isPathConnected_leftRegion _).preimage_coe hLR')
  have : PathConnectedSpace V' := by
    have h := (B.isPathConnected_middle hmm hcov).preimage_coe inter_subset_left
    have heq : ((↑) ⁻¹' (B.presentation.rightRegion (B.seam m) ∩
        B.presentation.rightRegion (B.seam m')) : Set ↥(B.presentation.rightRegion (B.seam m))) =
        V' := by
      ext z
      exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
    rw [heq] at h
    exact isPathConnected_iff_pathConnectedSpace.mp h
  have : PathConnectedSpace ↑(U' ∩ V') := by
    have h := (B.presentation.isPathConnected_seamCollar (B.seam m')).preimage_coe hCR
    have heq : ((↑) ⁻¹' B.presentation.seamCollar (B.seam m') :
        Set ↥(B.presentation.rightRegion (B.seam m))) = U' ∩ V' := by
      ext z
      change z.1 ∈ B.presentation.seamCollar (B.seam m') ↔
        z.1 ∈ B.presentation.leftRegion (B.seam m') ∩ B.presentation.rightRegion (B.seam m')
      rw [B.presentation.leftRegion_inter_rightRegion _ hsep']
    rw [heq] at h
    exact isPathConnected_iff_pathConnectedSpace.mp h
  let τ' : C(Torus, ↑(U' ∩ V')) :=
    ⟨fun t => ⟨⟨B.presentation.seamTorus (B.seam m') t,
      hCR (B.presentation.seamTorus_mem_seamCollar _ t)⟩,
      Or.inr (B.presentation.seamTorus_mem_seamCollar _ t),
      Or.inr (B.presentation.seamTorus_mem_seamCollar _ t)⟩,
      ((B.presentation.seamTorus _).continuous.subtype_mk _).subtype_mk _⟩
  have hmemC : ∀ z : ↑(U' ∩ V'), z.1.1 ∈ B.presentation.seamCollar (B.seam m') := fun z => by
    rw [← B.presentation.leftRegion_inter_rightRegion _ hsep']
    exact z.2
  let e : C(↑(U' ∩ V'), B.presentation.seamCollar (B.seam m')) :=
    ⟨fun z => ⟨z.1.1, hmemC z⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hmemC⟩
  let e' : C(B.presentation.seamCollar (B.seam m'), ↑(U' ∩ V')) :=
    ⟨fun w => ⟨⟨w.1, hCR w.2⟩, Or.inr w.2, Or.inr w.2⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  have hτ' : Function.Surjective (FundamentalGroup.map τ' torusBase) :=
    surjective_fundamentalGroup_map_of_comp_eq τ' e
      (B.presentation.seamTorusIn (B.seam m') _ le_rfl) (ContinuousMap.ext fun t => rfl) torusBase
      (injective_fundamentalGroup_map_of_leftInverse e e' (fun z => rfl) _)
      (B.presentation.bijective_seamTorusIn (B.seam m') _ rfl torusBase).2
  obtain ⟨f₁, hf₁⟩ := B.exists_leafRetraction m'
  let eU : C(U', B.presentation.leftRegion (B.seam m')) :=
    ⟨fun z => ⟨z.1.1, z.2⟩, (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let φ' : C(U', Circle) := (B.solid m').fibreMap.comp (f₁.comp eU)
  have hφ' : φ'.comp ((interToLeft U' V').comp τ') = ContinuousMap.snd := by
    refine ContinuousMap.ext fun t => ?_
    change (B.solid m').fibreMap (f₁ (B.presentation.seamTorusToLeft (B.seam m') t)) = t.2
    rw [hf₁]
    exact DFunLike.congr_fun ((B.solid m').fibreMap_comp_portMap 0) t
  let eV : C(V', ↥(B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m'))) :=
    ⟨fun z => ⟨z.1.1, z.1.2, z.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let yV := eV (interToRight U' V' (τ' torusBase))
  let fR' : FundamentalGroup V' (interToRight U' V' (τ' torusBase)) →* H :=
    ((ι.comp (B.product.productHom κ (f yV) (PathConnectedSpace.somePath b₀ _))).comp
      (FundamentalGroup.map f yV)).comp
        (FundamentalGroup.map eV (interToRight U' V' (τ' torusBase)))
  let p' : C(Torus, ↥(B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m'))) :=
    ⟨fun t => ⟨B.presentation.seamTorus (B.seam m') t,
      hCR (B.presentation.seamTorus_mem_seamCollar _ t),
      Or.inr (B.presentation.seamTorus_mem_seamCollar _ t)⟩,
      (B.presentation.seamTorus _).continuous.subtype_mk _⟩
  have hp' : f.comp p' =
      (B.product.portMap (B.port (.inr m'))).comp (B.presentation.matchingMap (B.seam m')) :=
    ContinuousMap.ext fun t => B.middle_seam f hf m' t _
  have hR' := forall_conj_pull eV
    ((ι.comp (B.product.productHom κ (f yV) (PathConnectedSpace.somePath b₀ _))).comp
      (FundamentalGroup.map f yV)) ((interToRight U' V').comp τ') torusBase _
    (forall_conj_congr _ (show eV.comp ((interToRight U' V').comp τ') = p' from
      ContinuousMap.ext fun t => rfl) torusBase _
      (B.forall_conj_product ι κ f yV (PathConnectedSpace.somePath b₀ _) p' _ _ hp' w' hκ'))
  obtain ⟨k₁, hk₁⟩ := hR' (Path.refl _)
  have hfR' : ∀ g, fR' (FundamentalGroup.map ((interToRight U' V').comp τ') torusBase g) =
      (k₁ * ι (w' ^ torusMapMatrix (B.presentation.matchingMap (B.seam m')) 0 1,
        ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m')) 1 1)) * k₁⁻¹) ^
          toAdd (GC.Topology.torusFundamentalGroup g).2 := by
    intro g
    rw [← markedMap_refl]
    refine (hk₁ g).trans ?_
    rw [port_matching_value ι w' _ hM' g, conj_zpow]
  obtain ⟨F₀, hF₀⟩ := exists_hom_glue_solid U' V' hU' hV' hcover' τ' hτ' φ' hφ' fR' _ hfR'
  refine ⟨(τ' torusBase).1, F₀, fun p c M hp w hκc => ?_⟩
  let p'' : C(Torus, V') := ⟨fun t => ⟨⟨(p t).1, (p t).2.1⟩, (p t).2.2⟩,
    (continuous_subtype_val.comp p.continuous).subtype_mk _ |>.subtype_mk _⟩
  refine forall_conj_congr F₀ (show (interToLeft (B.presentation.rightRegion (B.seam m))
    (B.presentation.rightRegion (B.seam m'))).comp p = (subsetToAmbient V').comp p'' from
      ContinuousMap.ext fun t => rfl) torusBase _ ?_
  refine forall_conj_push (subsetToAmbient V') (interToRight U' V' (τ' torusBase)) F₀ fR' hF₀ p''
    torusBase (PathConnectedSpace.somePath _ _) _ ?_
  refine forall_conj_pull eV _ p'' torusBase _ ?_
  refine forall_conj_congr _ (show eV.comp p'' = p from ContinuousMap.ext fun t => rfl)
    torusBase _ ?_
  exact B.forall_conj_product ι κ f yV (PathConnectedSpace.somePath b₀ _) p c M hp w hκc

end SeifertBlock

namespace SeifertBlock

open DifferentialGeometry.Topology.VanKampen

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem exists_core_hom (B : SeifertBlock W d) {m m' : Fin d.fillingCount} (hmm : m ≠ m')
    (hcov : ∀ n, n = m ∨ n = m') (r : Fin d.ports) {H : Type*} [Group H]
    (ι : FreeGroup (Fin 2) × Multiplicative ℤ →* H) {b₀ : B.product.base.surface.Carrier}
    (κ : FundamentalGroup B.product.base.surface.Carrier b₀ →* FreeGroup (Fin 2))
    (w w' wf : FreeGroup (Fin 2))
    (hκ : ∀ γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inr m)) 1),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m))) 1 γ a) =
          c' * w ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹)
    (hκ' : ∀ γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inr m')) 1),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m'))) 1 γ a) =
          c' * w' ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹)
    (hκf : ∀ γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inl r)) 1),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inl r))) 1 γ a) =
          c' * wf ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹)
    (hM : ι (w ^ torusMapMatrix (B.presentation.matchingMap (B.seam m)) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m)) 1 0)) = 1)
    (hM' : ι (w' ^ torusMapMatrix (B.presentation.matchingMap (B.seam m')) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m')) 1 0)) = 1) :
    ∃ Φ : FundamentalGroup W.Carrier
        (B.presentation.external.boundaryMap (B.free r) torusBase) →* H,
      ∀ g, Φ (FundamentalGroup.map (B.presentation.external.boundaryMap (B.free r)) torusBase g) =
        ι (wf ^ toAdd (GC.Topology.torusFundamentalGroup g).1,
          (GC.Topology.torusFundamentalGroup g).2) := by
  have := B.connectedSpace
  have hsep := B.isSeparating_seam m
  obtain ⟨f, hf⟩ := B.exists_middleRetraction hmm hcov
  obtain ⟨z₀, F₀, hF₀⟩ := B.exists_inner_hom hmm hcov ι κ f hf w' hκ' hM'
  obtain ⟨f₀, hf₀⟩ := B.exists_leafRetraction m
  have := B.presentation.pathConnectedSpace_inter (B.seam m) hsep
  let τ : C(Torus, ↑(B.presentation.leftRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m))) :=
    B.presentation.seamTorusIn (B.seam m) _
      (B.presentation.leftRegion_inter_rightRegion _ hsep).ge
  have hτ := (B.presentation.bijective_seamTorusIn (B.seam m) _
    (B.presentation.leftRegion_inter_rightRegion _ hsep) torusBase).2
  let φ : C(B.presentation.leftRegion (B.seam m), Circle) := (B.solid m).fibreMap.comp f₀
  have hφ : φ.comp ((interToLeft (B.presentation.leftRegion (B.seam m))
      (B.presentation.rightRegion (B.seam m))).comp τ) = ContinuousMap.snd := by
    refine ContinuousMap.ext fun t => ?_
    change (B.solid m).fibreMap (f₀ (B.presentation.seamTorusToLeft (B.seam m) t)) = t.2
    rw [hf₀]
    exact DFunLike.congr_fun ((B.solid m).fibreMap_comp_portMap 0) t
  let β₀ : Path z₀ (interToRight (B.presentation.leftRegion (B.seam m))
      (B.presentation.rightRegion (B.seam m)) (τ torusBase)) := PathConnectedSpace.somePath _ _
  let fR := F₀.comp (fundamentalGroupChangeBasepoint β₀).toMonoidHom
  have hC : ∀ t, B.presentation.seamTorus (B.seam m) t ∈ B.presentation.rightRegion (B.seam m') :=
    fun t => B.seamCollar_subset_rightRegion (Ne.symm hmm)
      (B.presentation.seamTorus_mem_seamCollar _ t)
  let p : C(Torus, ↥(B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m'))) :=
    ⟨fun t => ⟨B.presentation.seamTorus (B.seam m) t,
      Or.inr (B.presentation.seamTorus_mem_seamCollar _ t), hC t⟩,
      (B.presentation.seamTorus _).continuous.subtype_mk _⟩
  have hp : f.comp p =
      (B.product.portMap (B.port (.inr m))).comp (B.presentation.matchingMap (B.seam m)) :=
    ContinuousMap.ext fun t => B.middle_seam f hf m t _
  have hR := forall_conj_congr fR (show (interToRight (B.presentation.leftRegion (B.seam m))
      (B.presentation.rightRegion (B.seam m))).comp τ = (interToLeft (B.presentation.rightRegion
        (B.seam m)) (B.presentation.rightRegion (B.seam m'))).comp p from
      ContinuousMap.ext fun t => rfl) torusBase _
    (forall_conj_changeBasepoint F₀ β₀ _ torusBase _ (hF₀ p _ _ hp w hκ))
  obtain ⟨k₀, hk₀⟩ := hR (Path.refl _)
  have hfR : ∀ g, fR (FundamentalGroup.map ((interToRight (B.presentation.leftRegion (B.seam m))
      (B.presentation.rightRegion (B.seam m))).comp τ) torusBase g) =
      (k₀ * ι (w ^ torusMapMatrix (B.presentation.matchingMap (B.seam m)) 0 1,
        ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m)) 1 1)) * k₀⁻¹) ^
          toAdd (GC.Topology.torusFundamentalGroup g).2 := by
    intro g
    rw [← markedMap_refl]
    refine (hk₀ g).trans ?_
    rw [port_matching_value ι w _ hM g, conj_zpow]
  obtain ⟨F, hF⟩ := exists_hom_glue_solid _ _ (B.presentation.isOpen_leftRegion _)
    (B.presentation.isOpen_rightRegion _) (B.presentation.leftRegion_union_rightRegion _) τ hτ
    φ hφ fR _ hfR
  have hPR : ∀ x : B.presentation.components.piece (B.piece none),
      B.presentation.cutMap x ∈ B.presentation.rightRegion (B.seam m) ∩
        B.presentation.rightRegion (B.seam m') := fun x =>
    ⟨B.pieceImage_subset_rightRegion m (B.piece_some_ne_none m) ⟨x, x.2, rfl⟩,
      B.pieceImage_subset_rightRegion m' (B.piece_some_ne_none m') ⟨x, x.2, rfl⟩⟩
  let pf : C(Torus, ↥(B.presentation.rightRegion (B.seam m) ∩
      B.presentation.rightRegion (B.seam m'))) :=
    ⟨fun t => ⟨B.presentation.cutMap (B.product.portMap (B.port (.inl r)) t), hPR _⟩,
      ((B.presentation.pieceToCarrier _).comp (B.product.portMap _)).continuous.subtype_mk _⟩
  have hpf : f.comp pf = (B.product.portMap (B.port (.inl r))).comp (ContinuousMap.id Torus) :=
    ContinuousMap.ext fun t => hf _ _ rfl
  have hport : B.presentation.external.boundaryMap (B.free r) =
      (subsetToAmbient (B.presentation.rightRegion (B.seam m))).comp
        ((interToLeft (B.presentation.rightRegion (B.seam m))
          (B.presentation.rightRegion (B.seam m'))).comp pf) := by
    rw [B.external_boundaryMap_free]
    exact ContinuousMap.ext fun t => rfl
  have hconj := forall_conj_congr F hport torusBase _
    (forall_conj_push (subsetToAmbient (B.presentation.rightRegion (B.seam m)))
      (interToRight (B.presentation.leftRegion (B.seam m))
        (B.presentation.rightRegion (B.seam m)) (τ torusBase)) F fR hF _ torusBase
      (PathConnectedSpace.somePath _ _) _
      (forall_conj_changeBasepoint F₀ β₀ _ torusBase _ (hF₀ pf _ _ hpf wf hκf)))
  have : LocallyPathConnectedSpace W.Carrier :=
    Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model
  have : PathConnectedSpace W.Carrier := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  let δ := PathConnectedSpace.somePath (τ torusBase).1
    (B.presentation.external.boundaryMap (B.free r) torusBase)
  obtain ⟨k, hk⟩ := hconj δ
  refine ⟨(MulAut.conj k⁻¹).toMonoidHom.comp
    (F.comp (fundamentalGroupChangeBasepoint δ).toMonoidHom), fun g => ?_⟩
  have h := hk g
  rw [torusAut_id, MonoidHom.id_apply] at h
  change k⁻¹ * F (GC.Topology.markedMap _ torusBase δ g) * k⁻¹⁻¹ = _
  rw [h]
  group

end SeifertBlock

theorem PlanarBase.exists_pantsHom' {k : ℕ} (B : PlanarBase.{u} k) (hk : k = 3) {G : Type*}
    [Group G] (u v : G) :
    ∃ (b₀ : B.surface.Carrier) (κ : FundamentalGroup B.surface.Carrier b₀ →* G),
      ∀ (j : Fin k) (β : Path b₀ (B.boundaryCircle j 1)), ∃ c : G,
        ∀ a : FundamentalGroup Circle 1,
          κ (GC.Topology.markedMap (B.boundaryCircle j) 1 β a) =
            c * ![(v * u)⁻¹, u, v] (Fin.cast hk j) ^
              toAdd (fundamentalGroupCircleEquivInt a) * c⁻¹ := by
  subst hk
  exact B.exists_pantsHom u v

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem twoFillingDetection_of_fillingCount_eq_two (B : SeifertBlock W d)
    (hd : d.fillingCount = 2) (hst : ¬ d.IsSolidTorus) : B.TwoFillingDetection := by
  intro r
  have hk := d.ports_add_fillingCount
  have hk3 := d.k_le_three
  have hr := r.isLt
  have hk' : d.k = 3 := by omega
  have hports : d.ports = 1 := by omega
  have hnormals : d.normals.length = 0 := by
    simp only [SeifertData.IsSolidTorus, not_and, not_le] at hst
    have h2 := hst hports
    simp only [SeifertData.fillingCount] at hd
    omega
  let m₀ : Fin d.fillingCount := ⟨0, by omega⟩
  let m₁ : Fin d.fillingCount := ⟨1, by omega⟩
  have hmm : m₀ ≠ m₁ := fun h => absurd (congrArg Fin.val h) (by simp [m₀, m₁])
  have hcov : ∀ n, n = m₀ ∨ n = m₁ := fun n => by
    have hn := n.isLt
    rcases (by omega : n.val = 0 ∨ n.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hp2 : ∀ m : Fin d.fillingCount, 2 ≤ (d.fillingSlope m).1 := by
    intro m
    induction m using Fin.addCases with
    | left c =>
      rw [SeifertData.fillingSlope, Fin.append_left]
      have := d.two_le_of_mem_cones d.cones[c] (List.getElem_mem _)
      dsimp only
      omega
    | right n => exact absurd n.isLt (by omega)
  obtain ⟨P₀, hP₀⟩ : ∃ P : ℕ, (P : ℤ) = (d.fillingSlope m₀).1 :=
    ⟨_, Int.toNat_of_nonneg (by linarith [hp2 m₀])⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P : ℕ, (P : ℤ) = (d.fillingSlope m₁).1 :=
    ⟨_, Int.toNat_of_nonneg (by linarith [hp2 m₁])⟩
  have h2P₀ : 2 ≤ P₀ := by
    have := hp2 m₀
    omega
  have h2P₁ : 2 ≤ P₁ := by
    have := hp2 m₁
    omega
  let ι := twoFillingIncl (P₀ : ℤ) (d.fillingSlope m₀).2 0 0 (P₁ : ℤ) (d.fillingSlope m₁).2 0 0
  have hM₀ : ι (FreeGroup.of 0 ^ torusMapMatrix (B.presentation.matchingMap (B.seam m₀)) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m₀)) 1 0)) = 1 := by
    refine incl_relation_of_slope ι (FreeGroup.of 0) (twoFillingIncl_first _ _ _ _ _ _ _ _) ?_
    rw [hP₀]
    exact B.torusMatrix_meridian m₀
  have hM₁ : ι (FreeGroup.of 1 ^ torusMapMatrix (B.presentation.matchingMap (B.seam m₁)) 0 0,
      ofAdd (torusMapMatrix (B.presentation.matchingMap (B.seam m₁)) 1 0)) = 1 := by
    refine incl_relation_of_slope ι (FreeGroup.of 1) (twoFillingIncl_second _ _ _ _ _ _ _ _) ?_
    rw [hP₁]
    exact B.torusMatrix_meridian m₁
  obtain ⟨u', v', k', h0, h1, hf⟩ := exists_pants_values (Fin.cast hk' (B.port (.inr m₀)))
    (Fin.cast hk' (B.port (.inr m₁))) (Fin.cast hk' (B.port (.inl r)))
    (fun h => hmm (Sum.inr_injective (B.port.injective (Fin.cast_injective hk' h))))
    (fun h => Sum.inl_ne_inr (B.port.injective (Fin.cast_injective hk' h)))
    (fun h => Sum.inl_ne_inr (B.port.injective (Fin.cast_injective hk' h)))
  obtain ⟨b₀, κ, hκ⟩ := B.product.base.exists_pantsHom' hk' u' v'
  have hκ₀ : ∀ γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inr m₀)) 1),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m₀))) 1 γ a) =
          c' * FreeGroup.of 0 ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹ := by
    intro γ
    obtain ⟨c, hc⟩ := hκ _ γ
    exact ⟨c, fun a => by rw [hc a, h0]⟩
  have hκ₁ : ∀ γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inr m₁)) 1),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m₁))) 1 γ a) =
          c' * FreeGroup.of 1 ^ toAdd (fundamentalGroupCircleEquivInt a) * c'⁻¹ := by
    intro γ
    obtain ⟨c, hc⟩ := hκ _ γ
    exact ⟨c, fun a => by rw [hc a, h1]⟩
  have hκf : ∀ γ : Path b₀ (B.product.base.boundaryCircle (B.port (.inl r)) 1),
      ∃ c' : FreeGroup (Fin 2), ∀ a,
        κ (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inl r))) 1 γ a) =
          c' * (FreeGroup.of 0 * FreeGroup.of 1)⁻¹ ^ toAdd (fundamentalGroupCircleEquivInt a) *
            c'⁻¹ := by
    intro γ
    obtain ⟨c, hc⟩ := hκ _ γ
    refine ⟨c * k', fun a => ?_⟩
    rw [hc a, hf, conj_zpow]
    group
  obtain ⟨Φ, hΦ⟩ := B.exists_core_hom hmm hcov r ι κ _ _ _ hκ₀ hκ₁ hκf hM₀ hM₁
  refine ⟨P₀, P₁, (d.fillingSlope m₀).2, 0, 0, (d.fillingSlope m₁).2, 0, 0, Φ,
    invMonoidHom.prodMap (MonoidHom.id _), h2P₀, h2P₁, fun x y hxy => ?_, fun g => ?_⟩
  · exact Prod.ext (by simpa using congrArg Prod.fst hxy) (by simpa using congrArg Prod.snd hxy)
  · rw [hΦ, twoFillingPort_inv]

theorem isGoodBlock_of_twistedIBundle (B : TwistedIBundle W) : B.IsGoodBlock :=
  B.isGoodBlock_of_twoFillingDetection
    (B.twoFillingDetection_of_fillingCount_eq_two rfl not_isSolidTorus_twistedIBundleData)

end SeifertBlock

theorem filledBlockGoodness : FilledBlockGoodness.{u} := by
  intro W d B hports hst
  by_cases h1 : d.fillingCount ≤ 1
  · exact B.isGoodBlock_of_fillingCount_le_one hports hst h1
  · have hk := d.ports_add_fillingCount
    have hk3 := d.k_le_three
    exact B.isGoodBlock_of_twoFillingDetection
      (B.twoFillingDetection_of_fillingCount_eq_two (by omega) hst)

end GC.Seifert
