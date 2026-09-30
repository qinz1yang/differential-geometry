import DifferentialGeometry.Geometry.Metric.L2Product

set_option autoImplicit false

namespace IsometryEquiv

variable {X E A C : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace A] [MetricSpace C]

theorem exists_unique_l2ProductFactor_of_fst_eq
    (a : X ≃ᵢ WithLp 2 (E × A)) (c : X ≃ᵢ WithLp 2 (E × C))
    (hfst : ∀ x, (a x).fst = (c x).fst)
    {p : X} {e₀ : E} {a₀ : A} {c₀ : C}
    (ha : a p = WithLp.toLp 2 (e₀, a₀))
    (hc : c p = WithLp.toLp 2 (e₀, c₀)) :
    ∃! H : C ≃ᵢ A, H c₀ = a₀ ∧
      ∀ x, a x = WithLp.toLp 2 ((c x).fst, H (c x).snd) := by
  let f : C → A := fun q => (a (c.symm (WithLp.toLp 2 (e₀, q)))).snd
  let g : A → C := fun z => (c (a.symm (WithLp.toLp 2 (e₀, z)))).snd
  have haf (q : C) : a (c.symm (WithLp.toLp 2 (e₀, q))) =
      WithLp.toLp 2 (e₀, f q) := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · simpa using hfst (c.symm (WithLp.toLp 2 (e₀, q)))
    · rfl
  have hcg (z : A) : c (a.symm (WithLp.toLp 2 (e₀, z))) =
      WithLp.toLp 2 (e₀, g z) := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · simpa using (hfst (a.symm (WithLp.toLp 2 (e₀, z)))).symm
    · rfl
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro q r
    calc
      dist (f q) (f r) = dist (WithLp.toLp 2 (e₀, f q))
          (WithLp.toLp 2 (e₀, f r)) := ((WithLp.isometry_prodMk_left (Y := A) e₀).dist_eq (f q) (f r)).symm
      _ = dist q r := by rw [← haf, ← haf, a.dist_eq, c.symm.dist_eq,
        (WithLp.isometry_prodMk_left (Y := C) e₀).dist_eq q r]
  have hfg (z : A) : f (g z) = z := by
    dsimp only [f]
    rw [← hcg, c.symm_apply_apply, a.apply_symm_apply]
    rfl
  let H : C ≃ᵢ A := IsometryEquiv.mk' f g hfg hf
  have hH (q : C) : H q = f q := rfl
  have hpoint : H c₀ = a₀ := by
    rw [hH]
    dsimp only [f]
    rw [← hc, c.symm_apply_apply, ha]
    rfl
  have hglobal (x : X) : a x = WithLp.toLp 2 ((c x).fst, H (c x).snd) := by
    let y := c.symm (WithLp.toLp 2 (e₀, (c x).snd))
    have hay : a y = WithLp.toLp 2 (e₀, H (c x).snd) := haf _
    have hcy : c y = WithLp.toLp 2 (e₀, (c x).snd) := c.apply_symm_apply _
    have hd : dist (a x) (a y) = dist (c x) (c y) := by rw [a.dist_eq, c.dist_eq]
    have hsq := WithLp.prod_dist_sq_eq_add_sq (a x) (a y)
    rw [hd, WithLp.prod_dist_sq_eq_add_sq, hay, hcy] at hsq
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, hfst, dist_self,
      zero_pow (by decide : 2 ≠ 0), add_zero] at hsq
    have hz : dist (a x).snd (H (c x).snd) = 0 := by nlinarith [dist_nonneg (x := (a x).snd) (y := H (c x).snd)]
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext (hfst x) (dist_eq_zero.mp hz)
  refine ⟨H, ⟨hpoint, hglobal⟩, ?_⟩
  intro K hK
  apply IsometryEquiv.ext
  intro q
  have h := congrArg WithLp.snd (hK.2 (c.symm (WithLp.toLp 2 (e₀, q)))).symm
  simpa [f, H, IsometryEquiv.mk'] using h

end IsometryEquiv
