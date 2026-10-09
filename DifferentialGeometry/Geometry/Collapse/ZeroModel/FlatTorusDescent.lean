import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.Quotient

/-!
# The torus descent of a periodic cover, with its formula

Lane LFR54-Q0, group G3 (review 41, §5.6). Let `c : E → M` be an onto smooth local
diffeomorphism from a two-dimensional model space whose fibres are exactly the cosets of
`ℤ u + ℤ v` for linearly independent `u, v`. For every `q : E` there is a diffeomorphism
`Φ : ℝ/ℤ × ℝ/ℤ → M` with `Φ ([s], [t]) = c (q + s u + t v)`
(`exists_diffeomorph_addCircle_prod_apply_of_periodic_cover`).

This is the construction of `FlatSurface.nonempty_diffeomorph_addCircle_prod_of_periodic_cover`
(which exports only `Nonempty`), redone with the base point `q` and the descent formula: both
directions are descended through the periodic local diffeomorphisms `z ↦ c (q + z)` and
`z ↦ ([c₁ z], [c₂ z])` (coordinates in the basis `(u, v)`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
private theorem injective_mfderiv_coe_comp_LFR54Q0 (L : E →L[ℝ] ℝ) (y : E) :
    ∀ w w', mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y w =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y w' → L w = L w' := by
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y) :=
    AddCircle.contMDiff_coe.mdifferentiable (by simp) (L y)
  have hl : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y :=
    (L.contDiff (n := 1)).contMDiff.mdifferentiable (by simp) y
  have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y) :=
    mfderiv_comp (f := fun z => L z) (g := fun t : ℝ => (t : AddCircle (1 : ℝ))) y hc hl
  have hL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y = L := by
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  intro w w' h
  rw [hcomp, hL] at h
  exact (AddCircle.bijective_mfderiv_coe (L y)).1 h

private theorem addCircle_coe_eq_coe_iff_LFR54Q0 {a b : ℝ} :
    (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) ↔ ∃ m : ℤ, b - a = m := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [zsmul_eq_mul, mul_one] at hm
    exact ⟨m, by linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [zsmul_eq_mul, mul_one]; linarith⟩

/-- **Periodic descent with its formula** (review 41, §5.6). -/
theorem exists_diffeomorph_addCircle_prod_apply_of_periodic_cover (hdim : Module.finrank ℝ E = 2)
    {c : E → M} (hc : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ c) (hsurj : Surjective c)
    {u v : E} (hli : LinearIndependent ℝ ![u, v])
    (hfib : ∀ y z, c y = c z ↔ ∃ m n : ℤ, z - y = m • u + n • v) (q : E) :
    ∃ Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M,
      ∀ s t : ℝ, Φ ((s : AddCircle (1 : ℝ)), (t : AddCircle (1 : ℝ))) = c (q + s • u + t • v) := by
  let b : Module.Basis (Fin 2) ℝ E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : b 0 = u := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hb1 : b 1 = v := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  let c₁ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 0)
  let c₂ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord 1)
  have hrepr : ∀ z, c₁ z • u + c₂ z • v = z := by
    intro z
    have h := b.sum_repr z
    rw [Fin.sum_univ_two, hb0, hb1] at h
    exact h
  have hcoord : ∀ s t : ℝ, c₁ (s • u + t • v) = s ∧ c₂ (s • u + t • v) = t := by
    intro s t
    have h1 : b.repr (s • u + t • v) = Finsupp.single 0 s + Finsupp.single 1 t := by
      rw [← hb0, ← hb1, map_add, map_smul, map_smul, b.repr_self, b.repr_self,
        Finsupp.smul_single_one, Finsupp.smul_single_one]
    refine ⟨?_, ?_⟩
    · change b.repr (s • u + t • v) 0 = s
      rw [h1]
      simp
    · change b.repr (s • u + t • v) 1 = t
      rw [h1]
      simp
  -- the shifted cover and the torus coordinates
  let cov : E → M := fun z => c (q + z)
  let T : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E :=
    { toEquiv := Equiv.addLeft q
      contMDiff_toFun := by
        change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : E => q + z)
        exact (contDiff_const.add contDiff_id).contMDiff
      contMDiff_invFun := by
        change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : E => -q + z)
        exact (contDiff_const.add contDiff_id).contMDiff }
  have hcov : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov := fun z =>
    IsLocalDiffeomorphAt.comp (P := M) I (T.isLocalDiffeomorph z) (hc (q + z))
  have hcsurj : Surjective cov := fun x => by
    obtain ⟨y, hy⟩ := hsurj x
    exact ⟨-q + y, by simp only [cov, add_neg_cancel_left, hy]⟩
  let pair : E → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := fun z =>
    ((c₁ z : AddCircle (1 : ℝ)), (c₂ z : AddCircle (1 : ℝ)))
  have h₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (c₁ z : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp c₁.contDiff.contMDiff
  have h₂ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (c₂ z : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp c₂.contDiff.contMDiff
  have hpair_s : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ pair := h₁.prodMk h₂
  have hpair_inj : ∀ y, Injective (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) pair y) := by
    intro y w w' h
    rw [mfderiv_prodMk (h₁.mdifferentiableAt (by simp)) (h₂.mdifferentiableAt (by simp))] at h
    have e1 := injective_mfderiv_coe_comp_LFR54Q0 c₁ y w w' (congrArg Prod.fst h)
    have e2 := injective_mfderiv_coe_comp_LFR54Q0 c₂ y w w' (congrArg Prod.snd h)
    rw [← hrepr w, ← hrepr w', e1, e2]
  have hpair : IsLocalDiffeomorph 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ pair :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv pair hpair_s
      hpair_inj (by simp [hdim])
  have hpair_uv : ∀ s t : ℝ, pair (s • u + t • v) = ((s : AddCircle (1 : ℝ)), (t : AddCircle (1 : ℝ))) :=
    fun s t => by simp only [pair, (hcoord s t).1, (hcoord s t).2]
  have hpsurj : Surjective pair := by
    rintro ⟨x₁, x₂⟩
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x₁
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x₂
    exact ⟨s • u + t • v, hpair_uv s t⟩
  have hpair_eq : ∀ y z, pair y = pair z ↔ ∃ m n : ℤ, z - y = m • u + n • v := by
    intro y z
    simp only [pair, Prod.mk.injEq, addCircle_coe_eq_coe_iff_LFR54Q0]
    constructor
    · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
      refine ⟨m, n, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, ← hm, ← hn, sub_smul, sub_smul]
      conv_lhs => rw [← hrepr z, ← hrepr y]
      abel
    · rintro ⟨m, n, hmn⟩
      rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ] at hmn
      have hz : z = y + ((m : ℝ) • u + (n : ℝ) • v) := by rw [← hmn]; abel
      have hcz := hcoord (c₁ y + m) (c₂ y + n)
      have hz' : (c₁ y + m) • u + (c₂ y + n) • v = z := by
        rw [hz, add_smul, add_smul]
        conv_rhs => rw [← hrepr y]
        abel
      rw [hz'] at hcz
      exact ⟨⟨m, by rw [hcz.1]; ring⟩, ⟨n, by rw [hcz.2]; ring⟩⟩
  have hcompat : ∀ y z, cov y = cov z ↔ pair y = pair z := fun y z => by
    rw [hpair_eq, show (cov y = cov z) = (c (q + y) = c (q + z)) from rfl, hfib,
      add_sub_add_left_eq_sub]
  let φ : M → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := fun x => pair (surjInv hcsurj x)
  let ψ : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → M := fun x => cov (surjInv hpsurj x)
  have hφcov : ∀ z, φ (cov z) = pair z := fun z => (hcompat _ _).mp (surjInv_eq hcsurj (cov z))
  have hψp : ∀ z, ψ (pair z) = cov z := fun z => (hcompat _ _).mpr (surjInv_eq hpsurj (pair z))
  have hφs : ContMDiff I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ φ := by
    refine hcov.contMDiff_of_comp_of_surjective hcsurj ?_
    have h : φ ∘ cov = pair := funext hφcov
    rw [h]
    exact hpair_s
  have hψs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ ψ := by
    refine hpair.contMDiff_of_comp_of_surjective hpsurj ?_
    have h : ψ ∘ pair = cov := funext hψp
    rw [h]
    exact hcov.contMDiff
  have hleft : LeftInverse ψ φ := by
    intro x
    obtain ⟨z, rfl⟩ := hcsurj x
    rw [hφcov, hψp]
  have hright : RightInverse ψ φ := by
    intro x
    obtain ⟨z, rfl⟩ := hpsurj x
    rw [hψp, hφcov]
  refine ⟨{ toEquiv := ⟨ψ, φ, hright, hleft⟩, contMDiff_toFun := hψs, contMDiff_invFun := hφs },
    fun s t => ?_⟩
  change ψ ((s : AddCircle (1 : ℝ)), (t : AddCircle (1 : ℝ))) = c (q + s • u + t • v)
  rw [← hpair_uv, hψp, add_assoc]

end DifferentialGeometry.Geometry.Collapse.ZeroModel
