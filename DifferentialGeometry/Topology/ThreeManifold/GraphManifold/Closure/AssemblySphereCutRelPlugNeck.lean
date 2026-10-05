import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugMap
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelNeckApplications

/-!
# Chapter-14 assembly, relative COMPARE G4: the neck of the placed plug

Lane ASM-L2e, group G4. The two necks around the cut spheres — in `W` the seam collar between the
two shell charts, in the plug the seam collar between the two cap germs — correspond under the
placed plug.

* W side (`SphereCutCapped`, a fold off the caps `F`, shell charts `c`):
  `fold_capCore_sphere`, `F_capCore_sphere` (half collars of the cut spheres), `F_ne_sphere`
  (`F` misses the seam sphere), `F_shellChart_mem_neck` / `exists_shellChart_of_mem_neck` (the
  shell charts below radius `1 + η` fill exactly the neck `S.collar (S² × (-(s₀₁+μ₁η), s₀₀+μ₀η))`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- A positive-height point of a cut-sphere half collar is off the caps. -/
theorem capCore_sphere_not_mem_caps (j : Fin X.B.sphereCount) (z : ClosureSphere.{u}) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    X.capping.core (X.B.sphere j (z, halfPoint τ hτ0.le)) ∉ ⋃ i, range (X.capping.cap i) := by
  intro hcap
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcap
  have hmem : X.capping.core (X.B.sphere j (z, halfPoint τ hτ0.le)) ∈
      range X.capping.core ∩ range (X.capping.cap i) := ⟨⟨_, rfl⟩, hi⟩
  rw [X.capping.core_cap_intersection i] at hmem
  obtain ⟨z', hz'⟩ := hmem
  have he := X.core_injective' hz'
  have hs1 : (z, halfPoint τ hτ0.le) ∈ (X.B.sphere j).source := by
    rw [X.B.sphere_source]
    exact hτ1
  have hs0 : ∀ k, (z', halfZero) ∈ (X.B.sphere k).source := by
    intro k
    rw [X.B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  by_cases hij : i = j
  · subst hij
    have hp := (X.B.sphere i).injOn (hs0 i) hs1 he
    have hv : (0 : ℝ) = τ :=
      congrArg (fun q : ClosureSphere.{u} × EuclideanHalfSpace 1 => q.2.val 0) hp
    linarith
  · exact Set.disjoint_left.mp (X.B.sphere_disjoint hij) ((X.B.sphere i).map_source (hs0 i))
      (he ▸ (X.B.sphere j).map_source hs1)

variable {F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞}
  (hFs : F.source = (⋃ j, range (X.capping.cap j))ᶜ)
  (hF : ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y)

include hFs in
theorem capCore_sphere_mem_source (j : Fin X.B.sphereCount) (z : ClosureSphere.{u}) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    X.capping.core (X.B.sphere j (z, halfPoint τ hτ0.le)) ∈ F.source := by
  rw [hFs]
  exact X.capCore_sphere_not_mem_caps j z hτ0 hτ1

include hFs hF in
/-- `F` on the half collar of the cut sphere of side `t`. -/
theorem F_capCore_sphere (t : Fin 2) (z : ClosureSphere.{u}) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    F (X.capping.core (X.B.sphere (Fin.cast X.h2.symm t) (z, halfPoint τ hτ0.le))) =
      S.collar (z, if t.val = 0 then τ else -τ) := by
  rw [hF _ (X.capCore_sphere_mem_source hFs _ z hτ0 hτ1)]
  exact X.spheres t z τ hτ0.le hτ1

include hFs hF in
/-- `F` misses the seam sphere. -/
theorem F_ne_sphere {y : X.Q.Carrier} (hy : y ∈ F.source) (z : ClosureSphere.{u}) :
    F y ≠ S.collar (z, 0) := by
  intro he
  have hy' : y ∈ X.capComplement := by
    change y ∈ (⋃ j, range (X.capping.cap j))ᶜ
    rw [← hFs]
    exact hy
  obtain ⟨y', rfl⟩ := X.exists_core_eq hy'
  rw [hF y' hy, ← X.fold_sphere_zero (Fin.cast X.h2.symm 0) z] at he
  rcases X.fold_eq he with h | ⟨z', ⟨h, -⟩ | ⟨h, -⟩⟩
  · exact X.not_mem_sphere_of_core_mem hy' _ z h
  · exact X.not_mem_sphere_of_core_mem hy' _ z' h
  · exact X.not_mem_sphere_of_core_mem hy' _ z' h

section Shell

variable {X} {t : Fin 2} {c : PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞} {s₀ μ : ℝ}
  (hs₀ : 0 < s₀) (hμ : 0 < μ) (hsμ : s₀ + μ < 1)
  (hshell : ∀ (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
    c (r • (z : E3)) = X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
      (ULift.up z, halfPoint (s₀ + μ * (r - 1))
        (add_nonneg hs₀.le (mul_nonneg hμ.le (sub_nonneg.mpr hr))))))
  (hball : c '' ball 0 1 = range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
    X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t) '' {p | p.2.val 0 < s₀}))

include hFs hF hsμ hshell hball in
/-- **The shell chart below radius `1 + η` lies in the neck.** -/
theorem F_shellChart_mem_neck {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1) {w : E3} (hw : ‖w‖ < 1 + η)
    (hcw : c w ∈ F.source) :
    ∃ (z : ClosureSphere.{u}) (τ : ℝ), 0 < τ ∧ τ < s₀ + μ * η ∧
      F (c w) = S.collar (z, if t.val = 0 then τ else -τ) := by
  rcases lt_or_ge ‖w‖ 1 with hw1 | hw1
  · have hmem : c w ∈ c '' ball 0 1 := ⟨w, mem_ball_zero_iff.mpr hw1, rfl⟩
    rw [hball] at hmem
    rcases hmem with hcap | ⟨_, ⟨⟨z, h⟩, hp, rfl⟩, hcwe⟩
    · rw [hFs] at hcw
      exact (hcw (mem_iUnion.mpr ⟨_, hcap⟩)).elim
    · have hp' : h.val 0 < s₀ := hp
      rcases (h.2 : 0 ≤ h.val 0).lt_or_eq with hpos | hzero
      · have hh : h = halfPoint (h.val 0) h.2 := (halfPoint_eq_self h h.2 rfl).symm
        refine ⟨z, h.val 0, hpos, by nlinarith [mul_nonneg hμ.le hη0], ?_⟩
        rw [← hcwe, hh]
        exact X.F_capCore_sphere hFs hF t z hpos (by linarith)
      · have hh : h = halfZero := by
          apply Subtype.ext
          apply PiLp.ext
          intro k
          rw [Subsingleton.elim k 0]
          exact hzero.symm
        exfalso
        rw [hFs] at hcw
        apply hcw
        refine mem_iUnion.mpr ⟨Fin.cast X.h2.symm t, ?_⟩
        have hm : c w ∈ range fun z' => X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
            (z', halfZero)) := ⟨z, by rw [← hcwe, hh]⟩
        rw [← X.capping.core_cap_intersection] at hm
        exact hm.2
  · have hw0 : 0 < ‖w‖ := lt_of_lt_of_le one_pos hw1
    let z : sphere (0 : E3) 1 := ⟨‖w‖⁻¹ • w, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw0),
        inv_mul_cancel₀ hw0.ne']⟩
    have hwz : w = ‖w‖ • (z : E3) := by
      change w = ‖w‖ • (‖w‖⁻¹ • w)
      rw [smul_smul, mul_inv_cancel₀ hw0.ne', one_smul]
    have hτ0 : 0 < s₀ + μ * (‖w‖ - 1) := by nlinarith
    have hτ1 : s₀ + μ * (‖w‖ - 1) < 1 := by nlinarith
    refine ⟨ULift.up z, s₀ + μ * (‖w‖ - 1), hτ0, by nlinarith, ?_⟩
    have hc' := hshell z ‖w‖ hw1 (by linarith)
    rw [← hwz] at hc'
    rw [hc']
    exact X.F_capCore_sphere hFs hF t _ hτ0 hτ1

include hFs hF hshell hball in
/-- **Every neck point of side `t` comes from the shell chart below radius `1 + η`.** -/
theorem exists_shellChart_of_neck {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1) (hsμη : s₀ + μ * η < 1)
    (z : ClosureSphere.{u}) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < s₀ + μ * η) :
    ∃ w : E3, ‖w‖ < 1 + η ∧ c w ∈ F.source ∧
      F (c w) = S.collar (z, if t.val = 0 then τ else -τ) := by
  have hτ1 : τ < 1 := lt_trans hτ hsμη
  rcases lt_or_ge τ s₀ with hτs | hτs
  · have hmem : X.capping.core (X.B.sphere (Fin.cast X.h2.symm t) (z, halfPoint τ hτ0.le)) ∈
        c '' ball 0 1 := by
      rw [hball]
      exact Or.inr ⟨_, ⟨(z, halfPoint τ hτ0.le), hτs, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwe⟩ := hmem
    refine ⟨w, by have := mem_ball_zero_iff.mp hw; linarith, ?_, ?_⟩
    · rw [hwe]
      exact X.capCore_sphere_mem_source hFs _ z hτ0 hτ1
    · rw [hwe]
      exact X.F_capCore_sphere hFs hF t z hτ0 hτ1
  · let r : ℝ := 1 + (τ - s₀) / μ
    have hr1 : 1 ≤ r := by
      have : 0 ≤ (τ - s₀) / μ := div_nonneg (by linarith) hμ.le
      change 1 ≤ 1 + (τ - s₀) / μ
      linarith
    have hrη : r < 1 + η := by
      change 1 + (τ - s₀) / μ < 1 + η
      have : (τ - s₀) / μ < η := by rw [div_lt_iff₀ hμ]; linarith
      linarith
    have hheight : s₀ + μ * (r - 1) = τ := by
      change s₀ + μ * (1 + (τ - s₀) / μ - 1) = τ
      field_simp
      ring
    have hpt : halfPoint (s₀ + μ * (r - 1))
        (add_nonneg hs₀.le (mul_nonneg hμ.le (sub_nonneg.mpr hr1))) = halfPoint τ hτ0.le := by
      apply Subtype.ext
      apply PiLp.ext
      intro k
      exact hheight
    have hz1 : ‖z.down.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.down.property
    refine ⟨r • z.down.val, ?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hz1, mul_one]
      exact hrη
    · rw [hshell z.down r hr1 (by linarith), hpt]
      exact X.capCore_sphere_mem_source hFs _ z hτ0 hτ1
    · rw [hshell z.down r hr1 (by linarith), hpt]
      exact X.F_capCore_sphere hFs hF t z hτ0 hτ1

end Shell

end SphereCutCapped

/-! ### The plug side -/

namespace SolidCapPlug

variable {P : CompactCarrier.{u}} (Y : SolidCapPlug P)

theorem plugFold_source :
    Y.cut.capComplementFold.source = (⋃ j, range (Y.cut.capping.cap j))ᶜ :=
  Y.cut.capComplementFold_source

theorem plugFold_core (y : Y.cut.C.Carrier) (_ : Y.cut.capping.core y ∈ Y.cut.capComplementFold.source) :
    Y.cut.capComplementFold (Y.cut.capping.core y) = Y.cut.fold y :=
  Y.cut.capComplementFold_core y

/-- **The cap germ of the plug in the plug neck.** -/
theorem capChart_neck (t : Fin 2) (z : sphere (0 : E3) 1) {r : ℝ} (hr1 : 1 < r)
    (hr : r < 1 + Y.germ) :
    Y.capChart t (r • (z : E3)) ∈ Y.cut.capComplementFold.source ∧
      Y.cut.capComplementFold (Y.capChart t (r • (z : E3))) =
        Y.seam.collar (ULift.up z, if t.val = 0 then 2 * r - 2 else -(2 * r - 2)) := by
  have hτ0 : 0 < 2 * r - 2 := by linarith
  have hτ1 : 2 * r - 2 < 1 := by linarith [Y.germ_le]
  rw [Y.capChart_germ t z r hr1.le hr]
  exact ⟨Y.cut.capCore_sphere_mem_source Y.plugFold_source _ _ hτ0 hτ1,
    Y.cut.F_capCore_sphere Y.plugFold_source Y.plugFold_core t _ hτ0 hτ1⟩

/-- The neck of the plug. -/
def neckSet : Set P.Carrier := Y.seam.collar '' (univ ×ˢ Ioo (-(2 * Y.germ)) (2 * Y.germ))

theorem isOpen_neckSet : IsOpen Y.neckSet := by
  apply Y.seam.collar.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo)
  change _ ⊆ Y.seam.collar.source
  rw [Y.seam.source_eq]
  rintro p ⟨-, hp⟩
  have := Y.germ_le
  exact ⟨mem_univ _, by constructor <;> linarith [hp.1, hp.2]⟩

theorem mem_neckSet {z : ClosureSphere.{u}} {σ : ℝ} (hσ : |σ| < 2 * Y.germ) :
    Y.seam.collar (z, σ) ∈ Y.neckSet :=
  ⟨(z, σ), ⟨mem_univ _, (abs_lt.mp hσ).1, (abs_lt.mp hσ).2⟩, rfl⟩

theorem seam_symm_apply {z : ClosureSphere.{u}} {σ : ℝ} (hσ : |σ| < 1) :
    Y.seam.collar.symm (Y.seam.collar (z, σ)) = (z, σ) := by
  apply Y.seam.collar.left_inv
  rw [Y.seam.source_eq]
  exact ⟨mem_univ _, (abs_lt.mp hσ).1, (abs_lt.mp hσ).2⟩

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  {X : SphereCutCapped W S E}
  (F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞)
  (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier)
  (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
    (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
  (Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u})
  (h : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ)

/-- **The placed plug in `W`**: the reparametrised seam collar of `W` on the plug neck, the fold
off the caps of `W` after the placed plug elsewhere. -/
def placedPlugMap (y : P.Carrier) : W.Carrier :=
  haveI := Classical.propDecidable
  if y ∈ Y.neckSet then S.neckCollar h (Y.seam.collar.symm y)
  else F (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm y))

theorem placedPlugMap_of_mem {y : P.Carrier} (hy : y ∈ Y.neckSet) :
    Y.placedPlugMap F Ψ φ Θ h y = S.neckCollar h (Y.seam.collar.symm y) := by
  unfold placedPlugMap
  split_ifs
  rfl

theorem placedPlugMap_of_not_mem {y : P.Carrier} (hy : y ∉ Y.neckSet) :
    Y.placedPlugMap F Ψ φ Θ h y = F (Y.placedMap Ψ φ Θ (Y.cut.capComplementFold.symm y)) := by
  unfold placedPlugMap
  split_ifs
  rfl

theorem placedPlugMap_neck {z : ClosureSphere.{u}} {σ : ℝ} (hσ : |σ| < 2 * Y.germ) :
    Y.placedPlugMap F Ψ φ Θ h (Y.seam.collar (z, σ)) = S.collar (z, h σ) := by
  rw [Y.placedPlugMap_of_mem F Ψ φ Θ h (Y.mem_neckSet hσ),
    Y.seam_symm_apply (lt_of_lt_of_le hσ (by linarith [Y.germ_le]))]
  rfl

variable {Ψ φ Θ}

/-- The placed plug carries the cap charts onto the given ball charts. -/
theorem placedMap_capChart {c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞}
    (hmatch : ∀ t, ∀ x ∈ closedBall (0 : E3) 2,
      Ψ (c t x) = solidTubeFill (φ t) (Θ t (Y.solidChart t x)))
    (t : Fin 2) {x : E3} (hx : x ∈ closedBall (0 : E3) 2) :
    Y.placedMap Ψ φ Θ (Y.capChart t x) = c t x := by
  have hxs : x ∈ (Y.capChart t).source := Y.capChart_source t hx
  have hp : Y.capChart t x ∈ Y.piece t := Y.capChart_piece t ((Y.capChart t).map_source hxs)
  rw [Y.placedMap_of_mem Ψ φ Θ t hp]
  have he : (Y.solid t).symm ⟨Y.capChart t x, hp⟩ = Y.solidChart t x := by
    have h2 : (⟨Y.capChart t x, hp⟩ : Y.piece t) = Y.solid t (Y.solidChart t x) :=
      Subtype.ext (Y.solid_solidChart hxs).symm
    rw [h2, Diffeomorph.symm_apply_apply]
  change Ψ.symm (solidTubeFill (φ t) (Θ t ((Y.solid t).symm ⟨Y.capChart t x, hp⟩))) = _
  rw [he, ← hmatch t x hx, Diffeomorph.symm_apply_apply]

end SolidCapPlug

end GC.GraphManifold.Assembly
