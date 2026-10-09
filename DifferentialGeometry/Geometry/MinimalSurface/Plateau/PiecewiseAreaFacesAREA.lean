/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PiecewiseAreaConsumerAREA

/-!
# S-MY-AREA G5：3-face 开内部 a.e. disjoint ⇒ `∑_k A(u, α '' τ_k) ≤ A(u, D̄)`，10.3 的面积不等式 / 取等分析

G4 的 multiplicity 恒等式 `A(a) = ∑_k m_k A_k` 要变成 R12 `hcaps` 里的
`A(a₊) + A(a₋) ≤ 2 A(f)`，还差两步：

* `∑_k A_k ≤ A(f)`：不同 3-face 的开内部两两 a.e. disjoint（单纯复形的交
  `hull s ∩ hull t ⊆ hull (s ∩ t)`，而 `s ≠ t` 且都是 3 点集 ⇒ `s ∩ t` 至多 2 点，`hull` 在真仿射
  子空间里，零测）；`α` 在 `|T|` 上单射、Lipschitz 映零测到零测 ⇒ `α '' τ_k` 两两 a.e. disjoint，
  并含于 `D̄` ⇒ `∑_k A_k ≤ A(u, D̄)`（`sum_faces_area_le_AREA`）。
* multiplicity 的代数步（D-R-MY3-16）：`m₊,k + m₋,k ≤ 2` ⇒ `A(a₊) + A(a₋) ≤ 2 A(f)`
  （`caps_area_le_two_AREA`、`caps_diskArea_le_two_AREA`）；取等 ⇒ `∑_k A_k = A(f)` 且每个 `A_k > 0`
  的 face 有 `m₊,k + m₋,k = 2`（`caps_multiplicity_extremal_AREA`）；
  **不**推「每 cap 各覆盖一次」（`(2, 0)` / `(0, 2)` 未排除）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology ContDiff NNReal ENNReal Manifold

namespace DifferentialGeometry.Geometry

section Faces

/-- 两个不同的 3-face 的闭 hull 的交零测（`hull s ∩ hull t ⊆ hull (s ∩ t)`，`s ∩ t` 至多 2 点）。 -/
theorem volume_convexHull_inter_eq_zero_AREA {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    {s t : Finset ℂ} (hs : s ∈ T.faces) (ht : t ∈ T.faces) (hcs : s.card = 3)
    (hct : t.card = 3) (hne : s ≠ t) :
    volume (convexHull ℝ (s : Set ℂ) ∩ convexHull ℝ (t : Set ℂ)) = 0 := by
  have hsub : convexHull ℝ (s : Set ℂ) ∩ convexHull ℝ (t : Set ℂ) ⊆
      convexHull ℝ ((s ∩ t : Finset ℂ) : Set ℂ) := by
    rw [Finset.coe_inter]
    exact T.inter_subset_convexHull hs ht
  have hlt : s ∩ t ⊂ s := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, fun h => hne ?_⟩
    have hst : s ⊆ t := h ▸ Finset.inter_subset_right
    exact Finset.eq_of_subset_of_card_le hst (by omega)
  have hcard : (s ∩ t).card ≤ 2 := by
    have := Finset.card_lt_card hlt
    omega
  have hindep : AffineIndependent ℝ ((↑) : (s ∩ t : Finset ℂ) → ℂ) :=
    affineIndependent_of_subset (T.indep hs) Finset.inter_subset_left
  have hspan : affineSpan ℝ ((s ∩ t : Finset ℂ) : Set ℂ) ≠ ⊤ := by
    intro h
    have hr : range ((↑) : (s ∩ t : Finset ℂ) → ℂ) = ((s ∩ t : Finset ℂ) : Set ℂ) := by
      ext x
      simp
    have h' : affineSpan ℝ (range ((↑) : (s ∩ t : Finset ℂ) → ℂ)) = ⊤ := by rw [hr]; exact h
    have := hindep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp h'
    rw [Fintype.card_coe, Complex.finrank_real_complex] at this
    omega
  exact measure_mono_null (hsub.trans (convexHull_subset_affineSpan _))
    (Measure.addHaar_affineSubspace volume _ hspan)

/-- 不同的 3-face 的开内部两两 a.e. disjoint。 -/
theorem aedisjoint_openFace_AREA {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    {s t : Finset ℂ} (hs : s ∈ T.faces) (ht : t ∈ T.faces) (hcs : s.card = 3)
    (hct : t.card = 3) (hne : s ≠ t) :
    AEDisjoint volume (openFace_AREA s) (openFace_AREA t) :=
  measure_mono_null (inter_subset_inter (sdiff_subset.trans interior_subset)
    (sdiff_subset.trans interior_subset)) (volume_convexHull_inter_eq_zero_AREA hs ht hcs hct hne)

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- **G5a**：互异的 3-face 族 `face : κ → Finset ℂ` 的像面积之和不超过整盘面积：
`∑_k A(u, α '' τ_k) ≤ A(u, D̄)`。 -/
theorem sum_faces_area_le_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    {κ : Type*} [Fintype κ] (face : κ → Finset ℂ)
    (hface : ∀ k, face k ∈ T.faces ∧ (face k).card = 3) (hfinj : Function.Injective face) :
    ∑ k, riemannianArea g u (α '' openFace_AREA (face k)) ≤
      riemannianArea g u (closedBall 0 1) := by
  obtain ⟨K, hK⟩ := hprep.alpha_lip
  obtain ⟨Φ, hΦ, heΦ⟩ := hK.extend_finite_dimension
  have hτS (k : κ) : openFace_AREA (face k) ⊆ T.space :=
    openFace_subset_space_AREA (hface k).1
  have hBsub (k : κ) : α '' openFace_AREA (face k) ⊆ closedBall 0 1 :=
    (hprep.alpha_bij.mapsTo.mono_left (hτS k)).image_subset
  have hBm (k : κ) : MeasurableSet (α '' openFace_AREA (face k)) :=
    (isOpen_openFace_AREA _).measurableSet.image_of_continuousOn_injOn
      (hK.continuousOn.mono (hτS k)) (hprep.alpha_bij.injOn.mono (hτS k))
  have hd : Pairwise (fun i j => AEDisjoint volume (α '' openFace_AREA (face i))
      (α '' openFace_AREA (face j))) := by
    intro i j hij
    have hnull := aedisjoint_openFace_AREA (hface i).1 (hface j).1 (hface i).2 (hface j).2
      (hfinj.ne hij)
    have himg : volume (α '' (openFace_AREA (face i) ∩ openFace_AREA (face j))) = 0 := by
      rw [(heΦ.mono (inter_subset_left.trans (hτS i))).image_eq]
      exact DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitz hΦ hnull
    refine measure_mono_null ?_ himg
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have : b = a := hprep.alpha_bij.injOn (hτS j hb) (hτS i ha) hab
    exact ⟨a, ⟨ha, this ▸ hb⟩, rfl⟩
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hint : IntegrableOn (riemannianAreaDensity g u) (closedBall 0 1) :=
    integrableOn_riemannianAreaDensity_of_lipschitz g hu _
  rw [← riemannianArea_finite_decomposition g u (fun k => α '' openFace_AREA (face k)) hBm hd
    (hint.mono_set (iUnion_subset hBsub))]
  exact setIntegral_mono_set hint (Eventually.of_forall (riemannianAreaDensity_nonneg g u))
    (LE.le.eventuallySubset (iUnion_subset hBsub))

end Faces

section Algebra

/-- **multiplicity 的代数步**（D-R-MY3-16）：`m₊,k + m₋,k ≤ 2`、`A_k ≥ 0`、`∑ A_k ≤ B` ⇒
`A(a₊) + A(a₋) ≤ 2 B`。 -/
theorem caps_area_le_two_AREA {κ : Type*} [Fintype κ] (mp mm a : κ → ℝ) {Xp Xm B : ℝ}
    (hmult : ∀ k, mp k + mm k ≤ 2) (ha : ∀ k, 0 ≤ a k) (hsum : ∑ k, a k ≤ B)
    (hp : Xp = ∑ k, mp k * a k) (hm : Xm = ∑ k, mm k * a k) : Xp + Xm ≤ 2 * B := by
  have h1 : Xp + Xm = ∑ k, (mp k + mm k) * a k := by
    rw [hp, hm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (add_mul _ _ _).symm
  rw [h1]
  calc ∑ k, (mp k + mm k) * a k ≤ ∑ k, 2 * a k :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hmult k) (ha k)
    _ = 2 * ∑ k, a k := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * B := by linarith

/-- **取等分析**（D-R-MY3-16）：`A(a₊) + A(a₋) = 2 B` 时 `∑ A_k = B`，且每个 `A_k > 0` 的 face 有
`m₊,k + m₋,k = 2`；**不**推「每 cap 各覆盖一次」。 -/
theorem caps_multiplicity_extremal_AREA {κ : Type*} [Fintype κ] (mp mm a : κ → ℝ) {Xp Xm B : ℝ}
    (hmult : ∀ k, mp k + mm k ≤ 2) (ha : ∀ k, 0 ≤ a k) (hsum : ∑ k, a k ≤ B)
    (hp : Xp = ∑ k, mp k * a k) (hm : Xm = ∑ k, mm k * a k) (heq : Xp + Xm = 2 * B) :
    ∑ k, a k = B ∧ ∀ k, 0 < a k → mp k + mm k = 2 := by
  have h1 : Xp + Xm = ∑ k, (mp k + mm k) * a k := by
    rw [hp, hm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (add_mul _ _ _).symm
  have h2 : ∑ k, (2 - (mp k + mm k)) * a k = 2 * ∑ k, a k - (Xp + Xm) := by
    rw [h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ (2 - (mp k + mm k)) * a k := fun k _ =>
    mul_nonneg (by linarith [hmult k]) (ha k)
  have hS : ∑ k, a k = B := by
    have : 0 ≤ ∑ k, (2 - (mp k + mm k)) * a k := Finset.sum_nonneg hnn
    linarith
  refine ⟨hS, fun k hk => ?_⟩
  have hz : ∑ k, (2 - (mp k + mm k)) * a k = 0 := by rw [h2, heq, hS]; ring
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz k (Finset.mem_univ k)
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hk.ne'

end Algebra

section Hcaps

universe v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- **G5 的 consumer（R12 `hcaps` 面积子句）**：`ap, am` 的 `riemannianDiskArea` 满足
`cap_diskArea_multiplicity_AREA` 的 multiplicity 形（`mp k`, `mm k` 是各自的覆盖次数，
对互异的 3-face 族 `face`），且 `mp k + mm k ≤ 2`（D-R-MY3-16 的 producer 侧 bound）⇒
`A(ap) + A(am) ≤ 2 * A(f)`——正是 `top_caps_force_injective_R12` 的
`riemannianDiskArea g ap + riemannianDiskArea g am ≤ 2 * riemannianDiskArea g f` 子句。 -/
theorem caps_diskArea_le_two_AREA (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h) {C : ℝ≥0}
    (hf : ∀ x y : closedDisk, riemannianEDistOf g (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y)
    {κ : Type*} [Fintype κ] (face : κ → Finset ℂ)
    (hface : ∀ k, face k ∈ T.faces ∧ (face k).card = 3) (hfinj : Function.Injective face)
    {ap am : closedDisk → M} (mp mm : κ → ℝ) (hmult : ∀ k, mp k + mm k ≤ 2)
    (hp : riemannianDiskArea g ap = ∑ k, mp k *
      riemannianArea g (diskExtension f) (α '' openFace_AREA (face k)))
    (hm : riemannianDiskArea g am = ∑ k, mm k *
      riemannianArea g (diskExtension f) (α '' openFace_AREA (face k))) :
    riemannianDiskArea g ap + riemannianDiskArea g am ≤ 2 * riemannianDiskArea g f :=
  caps_area_le_two_AREA mp mm _ hmult (fun _ => riemannianArea_nonneg g _ _)
    (sum_faces_area_le_AREA g hprep (diskExtension_riemannian_lipschitz g hf) face hface hfinj)
    hp hm

end Hcaps

end DifferentialGeometry.Geometry
