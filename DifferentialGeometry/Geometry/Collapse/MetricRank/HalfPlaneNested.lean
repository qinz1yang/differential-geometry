import DifferentialGeometry.Geometry.Collapse.MetricRank.ProductIsometries
import DifferentialGeometry.Geometry.Collapse.MetricRank.HalfPlaneObstruction

/-!
# The nested product isometry for the thin half plane (S-X144c, group G11)

The closed upper half plane `H = {v ∈ ℝ² | 0 ≤ v 1}` (the boundary line is `{v 1 = 0}`, the
coordinate `v 0` runs along it and `v 1` is the distance to it) splits isometrically as
`H ≅ ℝ¹ ×₂ [0, ∞)`, `v ↦ (!₂[v 0], v 1)`. A product `H ×₂ Z` is therefore the
nested product `ℝ¹ ×₂ ([0, ∞) ×₂ Z)`, and a base point `(a, z)` is moved to `(0, ((a 1), z))` by
the translation `−a 0` of the first factor:

* `halfPlaneSplitIso_SMR` : `H ≃ᵢ ℝ¹ ×₂ [0, ∞)` (`v ↦ (!₂[v 0], ⟨v 1, _⟩)`);
* `halfPlaneNestedIso_SMR a` : `H ×₂ Z ≃ᵢ ℝ¹ ×₂ ([0, ∞) ×₂ Z)`, the composite of
  `prodCongrLeft_SMR halfPlaneSplitIso_SMR`, `prodAssocIso_SMR` and the translation of the first
  factor by `−!₂[a 0]`;
* `halfPlaneNestedIso_apply_base_SMR` : it sends `(a, z)` to `(0, ((a 1), z))`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

local notation "HP" => {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}
local notation "HR" => {t : ℝ // 0 ≤ t}

/-- The closed upper half plane is isometric to `ℝ¹ ×₂ [0, ∞)`. -/
noncomputable def halfPlaneSplitIso_SMR : HP ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × HR) where
  toFun v := WithLp.toLp 2 ((!₂[v.1 0] : EuclideanSpace ℝ (Fin 1)), (⟨v.1 1, v.2⟩ : HR))
  invFun w := ⟨!₂[w.fst 0, w.snd.1], by simpa using w.snd.2⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv w := by
    refine (WithLp.equiv 2 _).injective (Prod.ext ?_ (Subtype.ext ?_))
    · ext i
      fin_cases i
      simp
    · simp
  isometry_toFun := by
    refine Isometry.of_dist_eq fun v w => ?_
    have h := WithLp.prod_dist_sq_eq_add_sq
      (WithLp.toLp 2 ((!₂[v.1 0] : EuclideanSpace ℝ (Fin 1)), (⟨v.1 1, v.2⟩ : HR)))
      (WithLp.toLp 2 ((!₂[w.1 0] : EuclideanSpace ℝ (Fin 1)), (⟨w.1 1, w.2⟩ : HR)))
    have hv := norm_sq_fin_two_SMR (v.1 - w.1)
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h
    have h1 : dist (!₂[v.1 0] : EuclideanSpace ℝ (Fin 1))
        (!₂[w.1 0] : EuclideanSpace ℝ (Fin 1)) = dist (v.1 0) (w.1 0) :=
      realEuclideanOneIso_SMR.dist_eq _ _
    have h2 : dist (⟨v.1 1, v.2⟩ : HR) ⟨w.1 1, w.2⟩ = dist (v.1 1) (w.1 1) := rfl
    have hd : dist v w = ‖v.1 - w.1‖ := by rw [Subtype.dist_eq, dist_eq_norm]
    refine (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_
    rw [h, h1, h2, hd, hv]
    simp only [Real.dist_eq, sq_abs, PiLp.sub_apply]

/-- The nested isometry `H ×₂ Z ≃ᵢ ℝ¹ ×₂ ([0, ∞) ×₂ Z)`, translating the first factor by
`−!₂[a 0]` so that the base point `(a, z)` is sent to `(0, (a 1, z))`. -/
noncomputable def halfPlaneNestedIso_SMR {Z : Type*} [MetricSpace Z] (a : HP) :
    WithLp 2 (HP × Z) ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × WithLp 2 (HR × Z)) :=
  ((prodCongrLeft_SMR (Z := Z) halfPlaneSplitIso_SMR).trans prodAssocIso_SMR).trans
    (prodCongrLeft_SMR (IsometryEquiv.subRight (!₂[a.1 0] : EuclideanSpace ℝ (Fin 1))))

theorem halfPlaneNestedIso_apply_base_SMR {Z : Type*} [MetricSpace Z] (a : HP) (z : Z) :
    halfPlaneNestedIso_SMR a (WithLp.toLp 2 (a, z)) =
      WithLp.toLp 2 (0, WithLp.toLp 2 ((⟨a.1 1, a.2⟩ : HR), z)) := by
  change WithLp.toLp 2 ((!₂[a.1 0] : EuclideanSpace ℝ (Fin 1)) - !₂[a.1 0],
    WithLp.toLp 2 ((⟨a.1 1, a.2⟩ : HR), z)) = _
  rw [sub_self]

end GC.MetricGeometry
