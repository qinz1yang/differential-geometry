import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugNeck

/-!
# Chapter-14 assembly, relative COMPARE G4: the placed plug is an injective immersion into `W`

Lane ASM-L2e, group G4. For a solid-cap plug placed into two disjoint tubes of the capped carrier
of a sphere-cut `X` of `W` (the shape produced by G2), with a neck profile `h` gluing the two shell
germs, the map `SolidCapPlug.placedPlugMap` (`AssemblySphereCutRelPlugNeck`) is

* `placedMap_mem_source`: off the plug caps, the placed plug avoids the caps of `X`;
* `placedPlugMap_overlap`: on the overlap of the neck and the complement of its core it agrees with
  the fold of `W` after the placed plug (the two formulas glue);
* `neck_iff`: a point off the plug caps folds into the plug neck iff its placed image folds into
  the neck of `W` — the correspondence of the two necks;
* `contMDiff_placedPlugMap`, `bijective_mfderiv_placedPlugMap`, `injective_placedPlugMap`,
  `range_placedPlugMap`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace SolidCapPlug

variable {P : CompactCarrier.{u}} (Y : SolidCapPlug P)
  {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  {X : SphereCutCapped W S E}
  {F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞}
  (hFs : F.source = (⋃ j, range (X.capping.cap j))ᶜ)
  (hF : ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y)
  {Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier}
  {φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
    (PlaneLift.{u} × Circle) X.Q.Carrier ∞}
  (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
  (hφd : Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}))
  {c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞} {s₀ μ : Fin 2 → ℝ}
  (hs₀ : ∀ t, 0 < s₀ t) (hμ : ∀ t, 0 < μ t) (hsμ : ∀ t, s₀ t + μ t < 1)
  (hshell : ∀ t (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
    c t (r • (z : E3)) = X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
      (ULift.up z, halfPoint (s₀ t + μ t * (r - 1))
        (add_nonneg (hs₀ t).le (mul_nonneg (hμ t).le (sub_nonneg.mpr hr))))))
  (hball : ∀ t, c t '' ball 0 1 = range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
    X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t) '' {p | p.2.val 0 < s₀ t}))
  {Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}}
  (hmatch : ∀ t, ∀ x ∈ closedBall (0 : E3) 2,
    Ψ (c t x) = solidTubeFill (φ t) (Θ t (Y.solidChart t x)))

/-- A cap index of `X` is the cast of a side. -/
theorem cast_side (j : Fin X.B.sphereCount) : j = Fin.cast X.h2.symm (Fin.cast X.h2 j) := by
  ext
  rfl

/-- A cap index of the plug is the cast of a side. -/
theorem plug_cast_side (j : Fin Y.cut.B.sphereCount) :
    j = Fin.cast Y.cut.h2.symm (Fin.cast Y.cut.h2 j) := by
  ext
  rfl

include hball h3 hφd hmatch in
/-- A point whose placed image lies on a cap of `X` lies on a cap of the plug. -/
theorem mem_plugCap_of_placedMap_mem_cap {x : Y.cut.Q.Carrier} {j : Fin X.B.sphereCount}
    (hx : Y.placedMap Ψ φ Θ x ∈ range (X.capping.cap j)) :
    x ∈ ⋃ i, range (Y.cut.capping.cap i) := by
  rw [cast_side j] at hx
  set t := Fin.cast X.h2 j
  have hmem : Y.placedMap Ψ φ Θ x ∈ c t '' ball 0 1 := by
    rw [hball t]
    exact Or.inl hx
  obtain ⟨w, hw, hwe⟩ := hmem
  have hw2 : w ∈ closedBall (0 : E3) 2 := ball_subset_closedBall (ball_subset_ball (by norm_num) hw)
  rw [← Y.placedMap_capChart hmatch t hw2] at hwe
  have hxe := Y.injective_placedMap h3 hφd hwe
  refine mem_iUnion.mpr ⟨Fin.cast Y.cut.h2.symm t, ?_⟩
  rw [← Y.capChart_unit t, ← hxe]
  exact ⟨w, ball_subset_closedBall hw, rfl⟩

include hFs hball h3 hφd hmatch in
/-- **Off the plug caps, the placed plug avoids the caps of `X`.** -/
theorem placedMap_mem_source {x : Y.cut.Q.Carrier} (hx : x ∈ Y.cut.capComplementFold.source) :
    Y.placedMap Ψ φ Θ x ∈ F.source := by
  rw [hFs]
  intro hcap
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcap
  rw [Y.plugFold_source] at hx
  exact hx (Y.mem_plugCap_of_placedMap_mem_cap h3 hφd hball hmatch hj)

include hFs hF hshell in
/-- `F` on the shell chart of side `t`. -/
theorem F_shell (t : Fin 2) (z : sphere (0 : E3) 1) {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hτ1 : s₀ t + μ t * (r - 1) < 1) :
    c t (r • (z : E3)) ∈ F.source ∧
      F (c t (r • (z : E3))) = S.collar (ULift.up z,
        if t.val = 0 then s₀ t + μ t * (r - 1) else -(s₀ t + μ t * (r - 1))) := by
  have hτ0 : 0 < s₀ t + μ t * (r - 1) :=
    add_pos_of_pos_of_nonneg (hs₀ t) (mul_nonneg (hμ t).le (sub_nonneg.mpr hr))
  rw [hshell t z r hr hr2]
  exact ⟨X.capCore_sphere_mem_source hFs _ _ hτ0 hτ1, X.F_capCore_sphere hFs hF t _ hτ0 hτ1⟩

include hFs hF hshell hmatch in
/-- The positive half of the plug neck, through the fold off the caps and the placed plug. -/
theorem placed_seam_pos (hsμ : ∀ t, s₀ t + μ t < 1) (z : ClosureSphere.{u}) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : σ < 2 * Y.germ) :
    Y.seam.collar (z, σ) ∈ Y.cut.capComplementFold.target ∧
      Y.cut.capComplementFold.symm (Y.seam.collar (z, σ)) =
        Y.capChart 0 ((1 + σ / 2) • z.down.val) ∧
      F (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm (Y.seam.collar (z, σ)))) =
        S.collar (z, s₀ 0 + μ 0 * (σ / 2)) := by
  have hη := Y.germ_le
  obtain ⟨hsrc, hval⟩ := Y.capChart_neck 0 z.down (r := 1 + σ / 2) (by linarith) (by linarith)
  have hval' : Y.cut.capComplementFold (Y.capChart 0 ((1 + σ / 2) • z.down.val)) =
      Y.seam.collar (z, σ) := by
    rw [hval]
    congr 2
    simp only [Fin.val_zero, ↓reduceIte]
    ring
  have htgt : Y.seam.collar (z, σ) ∈ Y.cut.capComplementFold.target :=
    hval' ▸ Y.cut.capComplementFold.map_source hsrc
  have hsymm : Y.cut.capComplementFold.symm (Y.seam.collar (z, σ)) =
      Y.capChart 0 ((1 + σ / 2) • z.down.val) := by
    rw [← hval']
    exact Y.cut.capComplementFold.left_inv hsrc
  refine ⟨htgt, hsymm, ?_⟩
  have hn : (1 + σ / 2) • z.down.val ∈ closedBall (0 : E3) 2 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      mem_sphere_zero_iff_norm.mp z.down.property]
    linarith
  rw [hsymm, Y.placedMap_capChart hmatch 0 hn]
  have hF' := (F_shell hFs hF hs₀ hμ hshell 0 z.down (r := 1 + σ / 2) (by linarith)
    (by linarith) (by nlinarith [hsμ 0, hμ 0])).2
  rw [hF']
  congr 2
  simp only [Fin.val_zero, ↓reduceIte]
  ring

include hFs hF hshell hmatch in
/-- The negative half of the plug neck, through the fold off the caps and the placed plug. -/
theorem placed_seam_neg (hsμ : ∀ t, s₀ t + μ t < 1) (z : ClosureSphere.{u}) {σ : ℝ} (hσ0 : σ < 0)
    (hσ : -(2 * Y.germ) < σ) :
    Y.seam.collar (z, σ) ∈ Y.cut.capComplementFold.target ∧
      Y.cut.capComplementFold.symm (Y.seam.collar (z, σ)) =
        Y.capChart 1 ((1 - σ / 2) • z.down.val) ∧
      F (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm (Y.seam.collar (z, σ)))) =
        S.collar (z, -(s₀ 1 + μ 1 * (-σ / 2))) := by
  have hη := Y.germ_le
  obtain ⟨hsrc, hval⟩ := Y.capChart_neck 1 z.down (r := 1 - σ / 2) (by linarith) (by linarith)
  have hval' : Y.cut.capComplementFold (Y.capChart 1 ((1 - σ / 2) • z.down.val)) =
      Y.seam.collar (z, σ) := by
    rw [hval]
    congr 2
    simp only [Fin.val_one, one_ne_zero, ↓reduceIte]
    ring
  have htgt : Y.seam.collar (z, σ) ∈ Y.cut.capComplementFold.target :=
    hval' ▸ Y.cut.capComplementFold.map_source hsrc
  have hsymm : Y.cut.capComplementFold.symm (Y.seam.collar (z, σ)) =
      Y.capChart 1 ((1 - σ / 2) • z.down.val) := by
    rw [← hval']
    exact Y.cut.capComplementFold.left_inv hsrc
  refine ⟨htgt, hsymm, ?_⟩
  have hn : (1 - σ / 2) • z.down.val ∈ closedBall (0 : E3) 2 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      mem_sphere_zero_iff_norm.mp z.down.property]
    linarith
  rw [hsymm, Y.placedMap_capChart hmatch 1 hn]
  have hF' := (F_shell hFs hF hs₀ hμ hshell 1 z.down (r := 1 - σ / 2) (by linarith)
    (by linarith) (by nlinarith [hsμ 1, hμ 1])).2
  rw [hF']
  congr 2
  simp only [Fin.val_one, one_ne_zero, ↓reduceIte]
  ring

/-- A cap-chart point in the closed unit ball lies on a plug cap. -/
theorem capChart_not_mem_source (t : Fin 2) {w : E3} (hw : ‖w‖ ≤ 1) :
    Y.capChart t w ∉ Y.cut.capComplementFold.source := by
  rw [Y.plugFold_source]
  intro hn
  apply hn
  refine mem_iUnion.mpr ⟨Fin.cast Y.cut.h2.symm t, ?_⟩
  rw [← Y.capChart_unit t]
  exact ⟨w, mem_closedBall_zero_iff.mpr hw, rfl⟩

/-- A cap-chart point between radius one and `1 + germ` folds into the plug neck. -/
theorem capChart_mem_neckSet (t : Fin 2) {w : E3} (hw1 : 1 < ‖w‖) (hw : ‖w‖ < 1 + Y.germ) :
    Y.capChart t w ∈ Y.cut.capComplementFold.source ∧
      Y.cut.capComplementFold (Y.capChart t w) ∈ Y.neckSet := by
  have hw0 : 0 < ‖w‖ := lt_trans one_pos hw1
  let z : sphere (0 : E3) 1 := ⟨‖w‖⁻¹ • w, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw0),
      inv_mul_cancel₀ hw0.ne']⟩
  have hwz : ‖w‖ • (z : E3) = w := by
    change ‖w‖ • (‖w‖⁻¹ • w) = w
    rw [smul_smul, mul_inv_cancel₀ hw0.ne', one_smul]
  obtain ⟨hsrc, hval⟩ := Y.capChart_neck t z hw1 hw
  rw [hwz] at hsrc hval
  refine ⟨hsrc, ?_⟩
  rw [hval]
  apply Y.mem_neckSet
  split_ifs
  · rw [abs_of_pos (by linarith)]
    linarith
  · rw [abs_neg, abs_of_pos (by linarith)]
    linarith

/-- The neck of `W` between the heights `L` and `U`. -/
def neckW (S : SphereSeam W) (L U : ℝ) : Set W.Carrier := S.collar '' (univ ×ˢ Ioo L U)

theorem mem_neckW {L U : ℝ} (z : ClosureSphere.{u}) {τ : ℝ} (hL : L < τ) (hU : τ < U) :
    S.collar (z, τ) ∈ neckW S L U :=
  ⟨(z, τ), ⟨mem_univ _, hL, hU⟩, rfl⟩

include hFs hF h3 hφd hshell hball hmatch in
/-- **W neck ⇒ plug neck.** A point off the plug caps whose placed image folds into the neck of
`W` folds into the plug neck. -/
theorem mem_neckSet_of_mem_neckW (hsμ : ∀ t, s₀ t + μ t < 1) {x : Y.cut.Q.Carrier}
    (hx : x ∈ Y.cut.capComplementFold.source)
    (hT : F (Y.placedMap Ψ φ Θ x) ∈
      neckW S (-(s₀ 1 + μ 1 * Y.germ)) (s₀ 0 + μ 0 * Y.germ)) :
    Y.cut.capComplementFold x ∈ Y.neckSet := by
  have hη := Y.germ_le
  have hη0 := Y.germ_pos
  obtain ⟨⟨z, τ⟩, ⟨-, hτL, hτU⟩, hzτ⟩ := hT
  have hTs := Y.placedMap_mem_source hFs h3 hφd hball hmatch hx
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hzτ
    exact X.F_ne_sphere hFs hF hTs z hzτ.symm
  -- a shell chart point with the same image
  have hshellw : ∃ (t : Fin 2) (w : E3), ‖w‖ < 1 + Y.germ ∧ c t w ∈ F.source ∧
      F (c t w) = S.collar (z, τ) := by
    rcases lt_or_gt_of_ne hτ0 with hneg | hpos
    · obtain ⟨w, hw, hcw, hFw⟩ := X.exists_shellChart_of_neck hFs hF (hs₀ 1) (hμ 1) (hshell 1)
        (hball 1) hη0.le (by linarith) (by nlinarith [hsμ 1, hμ 1]) z (τ := -τ) (by linarith)
        (by linarith)
      refine ⟨1, w, hw, hcw, ?_⟩
      rw [hFw]
      simp
    · obtain ⟨w, hw, hcw, hFw⟩ := X.exists_shellChart_of_neck hFs hF (hs₀ 0) (hμ 0) (hshell 0)
        (hball 0) hη0.le (by linarith) (by nlinarith [hsμ 0, hμ 0]) z hpos hτU
      exact ⟨0, w, hw, hcw, by rw [hFw]; simp⟩
  obtain ⟨t, w, hw, hcw, hFw⟩ := hshellw
  have hTx : Y.placedMap Ψ φ Θ x = c t w := F.injOn hTs hcw (hzτ.symm.trans hFw.symm)
  have hw2 : w ∈ closedBall (0 : E3) 2 := mem_closedBall_zero_iff.mpr (by linarith)
  rw [← Y.placedMap_capChart hmatch t hw2] at hTx
  have hxe := Y.injective_placedMap h3 hφd hTx
  rcases le_or_gt ‖w‖ 1 with hw1 | hw1
  · exact (Y.capChart_not_mem_source t hw1 (hxe ▸ hx)).elim
  · rw [hxe]
    exact (Y.capChart_mem_neckSet t hw1 hw).2

include hFs hF hshell hmatch in
/-- **Plug neck ⇒ W neck.** -/
theorem mem_neckW_of_mem_neckSet (hsμ : ∀ t, s₀ t + μ t < 1) {x : Y.cut.Q.Carrier}
    (hx : x ∈ Y.cut.capComplementFold.source) (hN : Y.cut.capComplementFold x ∈ Y.neckSet) :
    F (Y.placedMap Ψ φ Θ x) ∈ neckW S (-(s₀ 1 + μ 1 * Y.germ)) (s₀ 0 + μ 0 * Y.germ) := by
  have hη := Y.germ_le
  obtain ⟨⟨z, σ⟩, ⟨-, hσL, hσU⟩, hzσ⟩ := hN
  have htgt := Y.cut.capComplementFold.map_source hx
  have hσ0 : σ ≠ 0 := by
    intro h0
    rw [h0] at hzσ
    rw [Y.cut.capComplementFold_target] at htgt
    exact htgt ⟨z, hzσ⟩
  have hxe : x = Y.cut.capComplementFold.symm (Y.seam.collar (z, σ)) := by
    rw [hzσ]
    exact (Y.cut.capComplementFold.left_inv hx).symm
  rcases lt_or_gt_of_ne hσ0 with hneg | hpos
  · obtain ⟨-, -, hF'⟩ := Y.placed_seam_neg hFs hF hs₀ hμ hshell hmatch hsμ z hneg hσL
    rw [hxe, hF']
    apply mem_neckW
    · nlinarith [hμ 1]
    · nlinarith [hs₀ 0, hs₀ 1, hμ 0, hμ 1]
  · obtain ⟨-, -, hF'⟩ := Y.placed_seam_pos hFs hF hs₀ hμ hshell hmatch hsμ z hpos hσU
    rw [hxe, hF']
    apply mem_neckW
    · nlinarith [hs₀ 0, hs₀ 1, hμ 0, hμ 1]
    · nlinarith [hμ 0]

include hFs hF hshell hball hmatch in
/-- A plug-cap point whose placed image is off the caps of `X` lands in the neck of `W`. -/
theorem mem_neckW_of_not_mem_source (hsμ : ∀ t, s₀ t + μ t < 1) {x : Y.cut.Q.Carrier}
    (hx : x ∉ Y.cut.capComplementFold.source) (hT : Y.placedMap Ψ φ Θ x ∈ F.source) :
    F (Y.placedMap Ψ φ Θ x) ∈ neckW S (-(s₀ 1 + μ 1 * Y.germ)) (s₀ 0 + μ 0 * Y.germ) := by
  have hη := Y.germ_le
  have hη0 := Y.germ_pos
  rw [Y.plugFold_source, mem_compl_iff, not_not] at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  rw [plug_cast_side Y j, ← Y.capChart_unit] at hj
  obtain ⟨w, hw, rfl⟩ := hj
  set t := Fin.cast Y.cut.h2 j
  have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
  have hw2 : w ∈ closedBall (0 : E3) 2 := mem_closedBall_zero_iff.mpr (by linarith)
  rw [Y.placedMap_capChart hmatch t hw2] at hT ⊢
  obtain ⟨z, τ, hτ0, hτ, hFw⟩ := X.F_shellChart_mem_neck hFs hF (hs₀ t) (hμ t) (hsμ t) (hshell t)
    (hball t) hη0.le (by linarith) (w := w) (by linarith) hT
  rw [hFw]
  by_cases ht : t.val = 0
  · have ht0 : t = 0 := Fin.ext ht
    simp only [ht, ↓reduceIte]
    rw [ht0] at hτ
    exact mem_neckW z (by nlinarith [hs₀ 1, hμ 1]) hτ
  · have ht1 : t = 1 := by
      have := t.isLt
      exact Fin.ext (by omega)
    simp only [ht, ↓reduceIte]
    rw [ht1] at hτ
    exact mem_neckW z (by linarith) (by nlinarith [hs₀ 0, hμ 0])

section Profile

variable (h : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ) {a : ℝ}

theorem profile_bounds (haη : a ≤ Y.germ) (hmono : StrictMono h)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ)
    {σ : ℝ} (hσ : |σ| < 2 * Y.germ) :
    -(s₀ 1 + μ 1 * Y.germ) < h σ ∧ h σ < s₀ 0 + μ 0 * Y.germ := by
  have hU : h (2 * Y.germ) = s₀ 0 + μ 0 * Y.germ := by
    rw [h₀ _ (by linarith [Y.germ_pos])]
    ring
  have hL : h (-(2 * Y.germ)) = -(s₀ 1 + μ 1 * Y.germ) := by
    rw [h₁ _ (by linarith [Y.germ_pos])]
    ring
  obtain ⟨h1, h2⟩ := abs_lt.mp hσ
  exact ⟨hL ▸ hmono h1, hU ▸ hmono h2⟩

theorem exists_profile_eq (haη : a ≤ Y.germ) (hmono : StrictMono h)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ)
    {τ : ℝ} (hL : -(s₀ 1 + μ 1 * Y.germ) < τ) (hU : τ < s₀ 0 + μ 0 * Y.germ) :
    ∃ σ, |σ| < 2 * Y.germ ∧ h σ = τ := by
  have hU' : h (2 * Y.germ) = s₀ 0 + μ 0 * Y.germ := by
    rw [h₀ _ (by linarith [Y.germ_pos])]
    ring
  have hL' : h (-(2 * Y.germ)) = -(s₀ 1 + μ 1 * Y.germ) := by
    rw [h₁ _ (by linarith [Y.germ_pos])]
    ring
  refine ⟨h.symm τ, abs_lt.mpr ⟨?_, ?_⟩, h.apply_symm_apply τ⟩
  · by_contra hc
    push Not at hc
    have := hmono.monotone hc
    rw [h.apply_symm_apply, hL'] at this
    linarith
  · by_contra hc
    push Not at hc
    have := hmono.monotone hc
    rw [h.apply_symm_apply, hU'] at this
    linarith

/-- The core of the plug neck. -/
def neckCore (a : ℝ) : Set P.Carrier := Y.seam.collar '' (univ ×ˢ Icc (-a) a)

/-- Off the core of the plug neck and off the plug sphere. -/
def offSet (a : ℝ) : Set P.Carrier := Y.cut.capComplementFold.target ∩ (Y.neckCore a)ᶜ

theorem isCompact_neckCore (ha1 : a < 1) : IsCompact (Y.neckCore a) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply Y.seam.collar.contMDiffOn_toFun.continuousOn.mono
  rw [Y.seam.source_eq]
  rintro p ⟨-, hp1, hp2⟩
  exact ⟨mem_univ _, by linarith [hp1], by linarith [hp2]⟩

theorem isOpen_offSet (ha1 : a < 1) : IsOpen (Y.offSet a) :=
  Y.cut.capComplementFold.open_target.inter (Y.isCompact_neckCore ha1).isClosed.isOpen_compl

theorem mem_neckSet_or_offSet (haη : a < 2 * Y.germ) (y : P.Carrier) :
    y ∈ Y.neckSet ∨ y ∈ Y.offSet a := by
  by_cases hy : y ∈ Y.neckSet
  · exact Or.inl hy
  · right
    refine ⟨?_, ?_⟩
    · rw [Y.cut.capComplementFold_target]
      rintro ⟨z, hz⟩
      apply hy
      rw [← hz]
      exact Y.mem_neckSet (by rw [abs_zero]; linarith [Y.germ_pos])
    · rintro ⟨p, ⟨-, hp1, hp2⟩, rfl⟩
      apply hy
      exact Y.mem_neckSet (abs_lt.mpr ⟨by linarith, by linarith⟩)

include hFs hF hshell hmatch in
/-- **The two formulas glue** on the plug neck off its core. -/
theorem placedPlugMap_overlap (hsμ : ∀ t, s₀ t + μ t < 1) (ha : 0 < a)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ)
    {y : P.Carrier} (hy : y ∈ Y.neckSet) (hy' : y ∉ Y.neckCore a) :
    y ∈ Y.cut.capComplementFold.target ∧
      Y.placedPlugMap F Ψ φ Θ h y = F (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm y)) := by
  obtain ⟨⟨z, σ⟩, ⟨-, hσL, hσU⟩, rfl⟩ := hy
  have hσ : |σ| < 2 * Y.germ := abs_lt.mpr ⟨hσL, hσU⟩
  rw [Y.placedPlugMap_neck F Ψ φ Θ h hσ]
  rcases le_or_gt σ (-a) with hneg | hσa
  · obtain ⟨htgt, -, hF'⟩ := Y.placed_seam_neg hFs hF hs₀ hμ hshell hmatch hsμ z
      (by linarith) hσL
    refine ⟨htgt, ?_⟩
    rw [hF', h₁ σ hneg]
    congr 2
    ring
  · rcases le_or_gt a σ with hpos | hsmall
    · obtain ⟨htgt, -, hF'⟩ := Y.placed_seam_pos hFs hF hs₀ hμ hshell hmatch hsμ z
        (by linarith) hσU
      refine ⟨htgt, ?_⟩
      rw [hF', h₀ σ hpos]
      congr 2
      ring
    · exact (hy' ⟨(z, σ), ⟨mem_univ _, hσa.le, hsmall.le⟩, rfl⟩).elim

include hFs hF hshell hmatch in
theorem placedPlugMap_of_offSet (hsμ : ∀ t, s₀ t + μ t < 1) (ha : 0 < a)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ)
    {y : P.Carrier} (hy : y ∈ Y.offSet a) :
    Y.placedPlugMap F Ψ φ Θ h y = F (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm y)) := by
  by_cases hN : y ∈ Y.neckSet
  · exact (Y.placedPlugMap_overlap hFs hF hs₀ hμ hshell hmatch h hsμ ha h₀ h₁ hN hy.2).2
  · exact Y.placedPlugMap_of_not_mem F Ψ φ Θ h hN

theorem neckSet_subset_target : Y.neckSet ⊆ Y.seam.collar.target := by
  rintro _ ⟨p, hp, rfl⟩
  apply Y.seam.collar.map_source
  rw [Y.seam.source_eq]
  have := Y.germ_le
  exact ⟨mem_univ _, by linarith [hp.2.1], by linarith [hp.2.2]⟩

theorem seam_symm_of_neckSet {y : P.Carrier} (hy : y ∈ Y.neckSet) :
    ∃ z σ, |σ| < 2 * Y.germ ∧ y = Y.seam.collar (z, σ) ∧ Y.seam.collar.symm y = (z, σ) := by
  obtain ⟨⟨z, σ⟩, ⟨-, hσL, hσU⟩, rfl⟩ := hy
  have hσ : |σ| < 2 * Y.germ := abs_lt.mpr ⟨hσL, hσU⟩
  exact ⟨z, σ, hσ, rfl, Y.seam_symm_apply (lt_of_lt_of_le hσ (by linarith [Y.germ_le]))⟩

include hμ in
theorem neck_mem_source (hsμ : ∀ t, s₀ t + μ t < 1) (haη : a ≤ Y.germ) (hmono : StrictMono h)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ)
    {y : P.Carrier} (hy : y ∈ Y.neckSet) :
    y ∈ (Y.seam.collar.symm.trans (S.neckCollar h)).source := by
  obtain ⟨z, σ, hσ, rfl, hsym⟩ := Y.seam_symm_of_neckSet hy
  refine ⟨Y.neckSet_subset_target hy, ?_⟩
  change Y.seam.collar.symm (Y.seam.collar (z, σ)) ∈ (S.neckCollar h).source
  rw [hsym, S.neckCollar_source]
  obtain ⟨hl, hu⟩ := Y.profile_bounds h haη hmono h₀ h₁ hσ
  have := Y.germ_le
  have hη0 := Y.germ_pos
  exact ⟨mem_univ _, by nlinarith [hsμ 1, hμ 1], by nlinarith [hsμ 0, hμ 0]⟩

include hFs hF h3 hφd hshell hball hmatch in
/-- **Smooth with bijective differentials.** -/
theorem contMDiffAt_placedPlugMap (hsμ : ∀ t, s₀ t + μ t < 1) (ha : 0 < a) (haη : a ≤ Y.germ)
    (hmono : StrictMono h)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ)
    (y : P.Carrier) :
    ContMDiffAt P.model W.model ∞ (Y.placedPlugMap F Ψ φ Θ h) y ∧
      Bijective (mfderiv P.model W.model (Y.placedPlugMap F Ψ φ Θ h) y) := by
  have hη := Y.germ_pos
  rcases Y.mem_neckSet_or_offSet (a := a) (by linarith) y with hy | hy
  · let N := Y.seam.collar.symm.trans (S.neckCollar h)
    have hyN : y ∈ N.source := Y.neck_mem_source hμ h hsμ haη hmono h₀ h₁ hy
    have hev : Y.placedPlugMap F Ψ φ Θ h =ᶠ[𝓝 y] N := by
      filter_upwards [Y.isOpen_neckSet.mem_nhds hy] with y' hy'
      rw [Y.placedPlugMap_of_mem F Ψ φ Θ h hy']
      rfl
    refine ⟨(N.contMDiffOn.contMDiffAt (N.open_source.mem_nhds hyN)).congr_of_eventuallyEq hev, ?_⟩
    rw [hev.mfderiv_eq]
    exact bijective_mfderiv_of_mem_source N hyN
  · have ha1 : a < 1 := by linarith [Y.germ_le]
    let G := F ∘ (Y.placedMap Ψ φ Θ ∘ Y.cut.capComplementFold.symm)
    have hev : Y.placedPlugMap F Ψ φ Θ h =ᶠ[𝓝 y] G := by
      filter_upwards [(Y.isOpen_offSet ha1).mem_nhds hy] with y' hy'
      exact Y.placedPlugMap_of_offSet hFs hF hs₀ hμ hshell hmatch h hsμ ha h₀ h₁ hy'
    have hyt : y ∈ Y.cut.capComplementFold.symm.source := hy.1
    have hxs : Y.cut.capComplementFold.symm y ∈ Y.cut.capComplementFold.source :=
      Y.cut.capComplementFold.map_target hy.1
    have hTs := Y.placedMap_mem_source hFs h3 hφd hball hmatch hxs
    have h1 : ContMDiffAt P.model Y.cut.Q.model ∞ Y.cut.capComplementFold.symm y :=
      Y.cut.capComplementFold.symm.contMDiffOn.contMDiffAt
        (Y.cut.capComplementFold.symm.open_source.mem_nhds hyt)
    have h2 : ContMDiffAt Y.cut.Q.model X.Q.model ∞ (Y.placedMap Ψ φ Θ)
        (Y.cut.capComplementFold.symm y) := (Y.contMDiff_placedMap h3).contMDiffAt
    have h3' : ContMDiffAt X.Q.model W.model ∞ F
        (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm y)) :=
      F.contMDiffOn.contMDiffAt (F.open_source.mem_nhds hTs)
    refine ⟨(h3'.comp y (h2.comp y h1)).congr_of_eventuallyEq hev, ?_⟩
    rw [hev.mfderiv_eq]
    have hb12 := bijective_mfderiv_comp (h1.mdifferentiableAt (by simp))
      (h2.mdifferentiableAt (by simp)) (bijective_mfderiv_of_mem_source _ hyt)
      (Y.bijective_mfderiv_placedMap h3 _)
    exact bijective_mfderiv_comp ((h2.comp y h1).mdifferentiableAt (by simp))
      (h3'.mdifferentiableAt (by simp)) hb12 (bijective_mfderiv_of_mem_source F hTs)

/-- The neck part lands in the neck of `W`. -/
theorem placedPlugMap_mem_neckW (haη : a ≤ Y.germ) (hmono : StrictMono h)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ)
    {y : P.Carrier} (hy : y ∈ Y.neckSet) :
    Y.placedPlugMap F Ψ φ Θ h y ∈ neckW S (-(s₀ 1 + μ 1 * Y.germ)) (s₀ 0 + μ 0 * Y.germ) := by
  obtain ⟨z, σ, hσ, rfl, -⟩ := Y.seam_symm_of_neckSet hy
  rw [Y.placedPlugMap_neck F Ψ φ Θ h hσ]
  obtain ⟨hl, hu⟩ := Y.profile_bounds h haη hmono h₀ h₁ hσ
  exact mem_neckW z hl hu

include hFs hF h3 hφd hshell hball hmatch in
/-- **The placed plug is injective.** -/
theorem injective_placedPlugMap (hsμ : ∀ t, s₀ t + μ t < 1) (ha : 0 < a) (haη : a ≤ Y.germ)
    (hmono : StrictMono h)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ) :
    Injective (Y.placedPlugMap F Ψ φ Θ h) := by
  have hη := Y.germ_pos
  have hη1 := Y.germ_le
  -- the off part is injective and misses the neck of `W`
  have hoff : ∀ {y : P.Carrier}, y ∉ Y.neckSet →
      y ∈ Y.cut.capComplementFold.target ∧
      Y.placedPlugMap F Ψ φ Θ h y =
        F (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm y)) ∧
      Y.placedPlugMap F Ψ φ Θ h y ∉
        neckW S (-(s₀ 1 + μ 1 * Y.germ)) (s₀ 0 + μ 0 * Y.germ) := by
    intro y hy
    have hyo := (Y.mem_neckSet_or_offSet (a := a) (by linarith) y).resolve_left hy
    have heq := Y.placedPlugMap_of_not_mem F Ψ φ Θ h hy
    refine ⟨hyo.1, heq, ?_⟩
    rw [heq]
    intro hN
    have hxs : Y.cut.capComplementFold.symm y ∈ Y.cut.capComplementFold.source :=
      Y.cut.capComplementFold.map_target hyo.1
    have := Y.mem_neckSet_of_mem_neckW hFs hF h3 hφd hs₀ hμ hshell hball hmatch hsμ hxs hN
    have hr : Y.cut.capComplementFold (Y.cut.capComplementFold.symm y) = y :=
      Y.cut.capComplementFold.right_inv hyo.1
    exact hy (hr ▸ this)
  intro y₁ y₂ he
  by_cases h1 : y₁ ∈ Y.neckSet <;> by_cases h2 : y₂ ∈ Y.neckSet
  · obtain ⟨z₁, σ₁, hσ₁, rfl, -⟩ := Y.seam_symm_of_neckSet h1
    obtain ⟨z₂, σ₂, hσ₂, rfl, -⟩ := Y.seam_symm_of_neckSet h2
    rw [Y.placedPlugMap_neck F Ψ φ Θ h hσ₁, Y.placedPlugMap_neck F Ψ φ Θ h hσ₂] at he
    have hb₁ := Y.profile_bounds h haη hmono h₀ h₁ hσ₁
    have hb₂ := Y.profile_bounds h haη hmono h₀ h₁ hσ₂
    have hs : ∀ (z : ClosureSphere.{u}) (σ : ℝ), -(s₀ 1 + μ 1 * Y.germ) < h σ →
        h σ < s₀ 0 + μ 0 * Y.germ → (z, h σ) ∈ S.collar.source := by
      intro z σ hl hu
      rw [S.source_eq]
      exact ⟨mem_univ _, by nlinarith [hsμ 1, hμ 1], by nlinarith [hsμ 0, hμ 0]⟩
    have hp := S.collar.injOn (hs z₁ σ₁ hb₁.1 hb₁.2) (hs z₂ σ₂ hb₂.1 hb₂.2) he
    simp only [Prod.mk.injEq] at hp
    rw [hp.1, hmono.injective hp.2]
  · exact ((hoff h2).2.2 (he ▸ Y.placedPlugMap_mem_neckW h haη hmono h₀ h₁ h1)).elim
  · exact ((hoff h1).2.2 (he.symm ▸ Y.placedPlugMap_mem_neckW h haη hmono h₀ h₁ h2)).elim
  · obtain ⟨ht₁, he₁, -⟩ := hoff h1
    obtain ⟨ht₂, he₂, -⟩ := hoff h2
    rw [he₁, he₂] at he
    have hx₁ := Y.cut.capComplementFold.map_target ht₁
    have hx₂ := Y.cut.capComplementFold.map_target ht₂
    have hT := F.injOn (Y.placedMap_mem_source hFs h3 hφd hball hmatch hx₁)
      (Y.placedMap_mem_source hFs h3 hφd hball hmatch hx₂) he
    have hx := Y.injective_placedMap h3 hφd hT
    exact Y.cut.capComplementFold.symm.injOn ht₁ ht₂ hx

include hFs hF h3 hφd hshell hball hmatch in
/-- **The image of the placed plug**: the fold of the placed closed unit tubes, plus the seam
sphere of `W`. -/
theorem range_placedPlugMap (hsμ : ∀ t, s₀ t + μ t < 1) (haη : a ≤ Y.germ)
    (hmono : StrictMono h)
    (h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ) (h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ) :
    range (Y.placedPlugMap F Ψ φ Θ h) =
      F '' ((Ψ.symm '' ⋃ t, φ t '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1}) ∩ F.source) ∪
        range (fun z => S.collar (z, 0)) := by
  have hη := Y.germ_pos
  have hη1 := Y.germ_le
  rw [← Y.range_placedMap (Ψ := Ψ) (φ := φ) (Θ := Θ)]
  -- a neck point of `W` off the seam sphere is a fold of a placed point
  have hneckW : ∀ (z : ClosureSphere.{u}) (τ : ℝ), τ ≠ 0 → -(s₀ 1 + μ 1 * Y.germ) < τ →
      τ < s₀ 0 + μ 0 * Y.germ →
      S.collar (z, τ) ∈ F '' (range (Y.placedMap Ψ φ Θ) ∩ F.source) := by
    intro z τ hτ0 hl hu
    have hfin : ∀ (t : Fin 2) (w : E3), ‖w‖ < 1 + Y.germ → c t w ∈ F.source →
        c t w ∈ range (Y.placedMap Ψ φ Θ) ∩ F.source := by
      intro t w hw hcw
      have hw2 : w ∈ closedBall (0 : E3) 2 := mem_closedBall_zero_iff.mpr (by linarith)
      exact ⟨⟨Y.capChart t w, Y.placedMap_capChart hmatch t hw2⟩, hcw⟩
    rcases lt_or_gt_of_ne hτ0 with hneg | hpos
    · obtain ⟨w, hw, hcw, hFw⟩ := X.exists_shellChart_of_neck hFs hF (hs₀ 1) (hμ 1) (hshell 1)
        (hball 1) hη.le (by linarith) (by nlinarith [hsμ 1, hμ 1]) z (τ := -τ) (by linarith)
        (by linarith)
      refine ⟨c 1 w, hfin 1 w hw hcw, ?_⟩
      rw [hFw]
      simp
    · obtain ⟨w, hw, hcw, hFw⟩ := X.exists_shellChart_of_neck hFs hF (hs₀ 0) (hμ 0) (hshell 0)
        (hball 0) hη.le (by linarith) (by nlinarith [hsμ 0, hμ 0]) z hpos hu
      exact ⟨c 0 w, hfin 0 w hw hcw, by rw [hFw]; simp⟩
  ext v
  constructor
  · rintro ⟨y, rfl⟩
    by_cases hy : y ∈ Y.neckSet
    · obtain ⟨z, σ, hσ, rfl, -⟩ := Y.seam_symm_of_neckSet hy
      rw [Y.placedPlugMap_neck F Ψ φ Θ h hσ]
      by_cases h0 : h σ = 0
      · exact Or.inr ⟨z, by rw [h0]⟩
      · obtain ⟨hl, hu⟩ := Y.profile_bounds h haη hmono h₀ h₁ hσ
        exact Or.inl (hneckW z (h σ) h0 hl hu)
    · have hyo := (Y.mem_neckSet_or_offSet (a := a) (by linarith) y).resolve_left hy
      rw [Y.placedPlugMap_of_not_mem F Ψ φ Θ h hy]
      have hxs := Y.cut.capComplementFold.map_target hyo.1
      exact Or.inl ⟨_, ⟨mem_range_self _, Y.placedMap_mem_source hFs h3 hφd hball hmatch hxs⟩, rfl⟩
  · rintro (⟨_, ⟨⟨x, rfl⟩, hv⟩, rfl⟩ | ⟨z, rfl⟩)
    · by_cases hN : F (Y.placedMap Ψ φ Θ x) ∈
          neckW S (-(s₀ 1 + μ 1 * Y.germ)) (s₀ 0 + μ 0 * Y.germ)
      · obtain ⟨⟨z, τ⟩, ⟨-, hl, hu⟩, hzτ⟩ := hN
        obtain ⟨σ, hσ, hστ⟩ := Y.exists_profile_eq h haη hmono h₀ h₁ hl hu
        refine ⟨Y.seam.collar (z, σ), ?_⟩
        rw [Y.placedPlugMap_neck F Ψ φ Θ h hσ, hστ]
        exact hzτ
      · have hx : x ∈ Y.cut.capComplementFold.source := by
          by_contra hx
          exact hN (Y.mem_neckW_of_not_mem_source hFs hF hs₀ hμ hshell hball hmatch hsμ hx hv)
        have hy : Y.cut.capComplementFold x ∉ Y.neckSet := fun hy =>
          hN (Y.mem_neckW_of_mem_neckSet hFs hF hs₀ hμ hshell hmatch hsμ hx hy)
        refine ⟨Y.cut.capComplementFold x, ?_⟩
        have hl : Y.cut.capComplementFold.symm (Y.cut.capComplementFold x) = x :=
          Y.cut.capComplementFold.left_inv hx
        rw [Y.placedPlugMap_of_not_mem F Ψ φ Θ h hy, hl]
    · obtain ⟨σ, hσ, hστ⟩ := Y.exists_profile_eq h haη hmono h₀ h₁ (τ := 0)
        (by nlinarith [hs₀ 1, hμ 1]) (by nlinarith [hs₀ 0, hμ 0])
      refine ⟨Y.seam.collar (z, σ), ?_⟩
      rw [Y.placedPlugMap_neck F Ψ φ Θ h hσ, hστ]

end Profile

end SolidCapPlug

end GC.GraphManifold.Assembly
