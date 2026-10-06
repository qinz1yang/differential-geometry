import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicPrimitive

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set Function GC.Endpoint
open scoped Manifold ContDiff ContinuousMap
namespace GC.LongTime.CuspP1

private theorem addCircle_coe_eq_coe_iff_CPA2 {a b : ℝ} :
    (a : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) ↔ ∃ m : ℤ, b - a = m := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [zsmul_eq_mul, mul_one] at hm
    exact ⟨m, by linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [zsmul_eq_mul, mul_one]; linarith⟩

/-- Lattice cover of the torus: a self-homeomorphism `h` with `h (z^a, z^b) = F (s (a v₁ + b v₂))`
for `z = exp(2πi s)`. -/
theorem exists_homeo_of_lattice_cover_rays_CPA3 (F : TorusPlane → Torus) (v₁ v₂ : TorusPlane)
    (hF : Continuous F) (hFs : Surjective F) (hli : LinearIndependent ℝ ![v₁, v₂])
    (hfib : ∀ y z, F y = F z ↔ ∃ m n : ℤ, z - y = m • v₁ + n • v₂) :
    ∃ h : Torus ≃ₜ Torus, ∀ (a b : ℤ) (s : ℝ),
      h (phiC (s : AddCircle (1 : ℝ)) ^ a, phiC (s : AddCircle (1 : ℝ)) ^ b) =
        F (s • (a • v₁ + b • v₂)) := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ TorusPlane := by
    simp
  let b : Module.Basis (Fin 2) ℝ TorusPlane := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = v₁ := by simp [b]
  have hb1 : b 1 = v₂ := by simp [b]
  let L : TorusPlane ≃L[ℝ] ℝ × ℝ :=
    (b.equivFun.toContinuousLinearEquiv).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hL1 : L v₁ = (1, 0) := by
    rw [← hb0]
    ext <;> simp [L, Module.Basis.equivFun_apply]
  have hL2 : L v₂ = (0, 1) := by
    rw [← hb1]
    ext <;> simp [L, Module.Basis.equivFun_apply]
  have hLlat : ∀ (m n : ℤ), L (m • v₁ + n • v₂) = ((m : ℝ), (n : ℝ)) := by
    intro m n
    rw [map_add, map_zsmul, map_zsmul, hL1, hL2]
    ext <;> simp
  let ψ : ℝ → Circle := fun t => phiC (t : AddCircle (1 : ℝ))
  have hψc : Continuous ψ := phiC.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hψo : IsOpenMap ψ :=
    phiC.isOpenMap.comp (QuotientAddGroup.isOpenMap_coe (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ)))
  have hψs : Surjective ψ := fun c => by
    obtain ⟨u, rfl⟩ := phiC.surjective c
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective u
    exact ⟨t, rfl⟩
  have hψeq : ∀ a c : ℝ, ψ a = ψ c ↔ ∃ m : ℤ, c - a = m := fun a c => by
    rw [← addCircle_coe_eq_coe_iff_CPA2]
    exact phiC.injective.eq_iff
  let Q : TorusPlane → Torus := fun y => (ψ (L y).1, ψ (L y).2)
  have hQc : Continuous Q :=
    (hψc.comp (continuous_fst.comp L.continuous)).prodMk (hψc.comp (continuous_snd.comp L.continuous))
  have hQo : IsOpenMap Q := by
    have : Q = Prod.map ψ ψ ∘ L := rfl
    rw [this]
    exact (hψo.prodMap hψo).comp L.isOpenMap
  have hQs : Surjective Q := by
    rintro ⟨c, d⟩
    obtain ⟨s, rfl⟩ := hψs c
    obtain ⟨t, rfl⟩ := hψs d
    exact ⟨L.symm (s, t), by simp [Q]⟩
  have hQq : _root_.Topology.IsQuotientMap Q := hQo.isQuotientMap hQc hQs
  have hQfib : ∀ y z, Q y = Q z ↔ F y = F z := by
    intro y z
    rw [hfib]
    constructor
    · intro h
      have h1 := (hψeq _ _).mp (congrArg Prod.fst h)
      have h2 := (hψeq _ _).mp (congrArg Prod.snd h)
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      refine ⟨m, n, L.injective ?_⟩
      rw [hLlat, map_sub]
      ext
      · exact hm
      · exact hn
    · rintro ⟨m, n, hmn⟩
      have h := congrArg L hmn
      rw [hLlat, map_sub] at h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
      exact Prod.ext ((hψeq _ _).mpr ⟨m, h1⟩) ((hψeq _ _).mpr ⟨n, h2⟩)
  obtain ⟨h, hh⟩ := exists_homeo_of_same_fibres_CPA2 Q F hQq hF hFs hQfib
  refine ⟨h, fun a b s => ?_⟩
  rw [← hh (s • (a • v₁ + b • v₂))]
  have hLs : L (s • (a • v₁ + b • v₂)) = (s * a, s * b) := by
    rw [map_smul, hLlat]; ext <;> simp
  have hpow : ∀ n : ℤ, ψ (s * n) = phiC (s : AddCircle (1 : ℝ)) ^ n := by
    intro n
    have : ((s * n : ℝ) : AddCircle (1 : ℝ)) = n • (s : AddCircle (1 : ℝ)) := by
      rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul, mul_comm]
    simp only [ψ, this, phiC, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zsmul]
  have : Q (s • (a • v₁ + b • v₂)) = (phiC (s : AddCircle (1 : ℝ)) ^ a, phiC (s : AddCircle (1 : ℝ)) ^ b) := by
    simp only [Q, hLs]
    rw [hpow, hpow]
  rw [this]

end GC.LongTime.CuspP1
