/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Affine.Crystallographic.CocompactActions
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.TranslationLattices

noncomputable section

open Set

namespace DifferentialGeometry.AffineCrystallographic

open DifferentialGeometry.CrystallographicActions Horospherical

variable {G : Type*} [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem translation_kernel_nilpotent (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hinj : Function.Injective ρ) : Group.IsNilpotent (linearPart.comp ρ).ker :=
  (Group.isNilpotent_congr (translationEquiv ρ hinj)).mp inferInstance

theorem translation_kernel_le (ρ σ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hcoσ : CoboundedOrbit σ) [(linearPart.comp ρ).ker.FiniteIndex] :
    (linearPart.comp ρ).ker ≤ (linearPart.comp σ).ker := by
  let T := (linearPart.comp ρ).ker
  let := translation_kernel_nilpotent ρ hρ
  have ht := nilpotent_is_translation (σ.comp T.subtype)
    (hσ.comp T.subtype_injective) (coboundedOrbit_finiteIndex σ hcoσ T)
  intro g hg
  exact linearPart_eq_one_of_translation (σ g) (ht ⟨g, hg⟩)

theorem translation_kernel_eq (ρ σ : G →* (E ≃ᵃⁱ[ℝ] E))
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hcoρ : CoboundedOrbit ρ) (hcoσ : CoboundedOrbit σ)
    (hvirt : Group.IsVirtuallyNilpotent G) :
    (linearPart.comp ρ).ker = (linearPart.comp σ).ker := by
  let := finiteIndex_linear_kernel ρ hρ hcoρ hvirt
  let := finiteIndex_linear_kernel σ hσ hcoσ hvirt
  exact le_antisymm (translation_kernel_le ρ σ hρ hσ hcoσ)
    (translation_kernel_le σ ρ hσ hρ hcoρ)

theorem translationVector_conj (ρ : G →* (E ≃ᵃⁱ[ℝ] E))
    (g t : G) (ht : t ∈ (linearPart.comp ρ).ker) :
    ρ (g * t * g⁻¹) 0 = (ρ g).linearIsometryEquiv (ρ t 0) := by
  have hi : ρ g (ρ g⁻¹ 0) = 0 := by
    change (ρ g * ρ g⁻¹) 0 = 0
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [map_mul, map_mul]
  change ρ g (ρ t (ρ g⁻¹ 0)) = _
  rw [translation_of_linearPart_eq_one (ρ t) ht,
    affine_eq_linear_add (ρ g), map_add]
  have he : (ρ g).linearIsometryEquiv (ρ g⁻¹ 0) + ρ g 0 = 0 :=
    (affine_eq_linear_add (ρ g) (ρ g⁻¹ 0)).symm.trans hi
  calc
    _ = (ρ g).linearIsometryEquiv (ρ t 0) +
        ((ρ g).linearIsometryEquiv (ρ g⁻¹ 0) + ρ g 0) := by abel
    _ = _ := by rw [he, add_zero]

section LatticeExtension

variable {m : ℕ}

theorem exists_linear_extension (ρ σ : G →* (Horizontal m ≃ᵃⁱ[ℝ] Horizontal m))
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hcoρ : CoboundedOrbit ρ) (hcoσ : CoboundedOrbit σ)
    (hpρ : ∀ B : ℝ, {g : G | ‖ρ g 0‖ ≤ B}.Finite)
    (hpσ : ∀ B : ℝ, {g : G | ‖σ g 0‖ ≤ B}.Finite)
    (hvirt : Group.IsVirtuallyNilpotent G) :
    ∃ L : Horizontal m ≃L[ℝ] Horizontal m,
      ∀ t : (linearPart.comp ρ).ker, L (ρ (t : G) 0) = σ (t : G) 0 := by
  let D := translationModule ρ
  let D' := translationModule σ
  let : DiscreteTopology D := discrete_translationModule ρ hpρ
  let : DiscreteTopology D' := discrete_translationModule σ hpσ
  let : IsZLattice ℝ D := isZLattice_translationModule ρ hρ hcoρ hvirt
  let : IsZLattice ℝ D' := isZLattice_translationModule σ hσ hcoσ hvirt
  let eρ := translationEquiv ρ hρ
  let eσ := translationEquiv σ hσ
  let eK := MulEquiv.subgroupCongr (translation_kernel_eq ρ σ hρ hσ hcoρ hcoσ hvirt)
  let e : Multiplicative D ≃* Multiplicative D' := eρ.trans (eK.trans eσ.symm)
  let eD : D ≃+ D' :=
    { toFun := fun u => (e (Multiplicative.ofAdd u)).toAdd
      invFun := fun u => (e.symm (Multiplicative.ofAdd u)).toAdd
      left_inv := fun u => congrArg Multiplicative.toAdd (e.symm_apply_apply (Multiplicative.ofAdd u))
      right_inv := fun u => congrArg Multiplicative.toAdd (e.apply_symm_apply (Multiplicative.ofAdd u))
      map_add' := fun u v => congrArg Multiplicative.toAdd
        (e.map_mul (Multiplicative.ofAdd u) (Multiplicative.ofAdd v)) }
  obtain ⟨L, hL⟩ := TranslationLattices.exists_linear_extension D D' eD
  refine ⟨L, fun t => ?_⟩
  obtain ⟨u, rfl⟩ := eρ.surjective t
  have hsrc : ρ (eρ u : G) 0 = (u.toAdd : Horizontal m) := by
    simpa only [zero_add] using translationEquiv_apply ρ hρ u 0
  have he : (eσ (e u) : G) = (eρ u : G) := by
    change (eσ (eσ.symm (eK (eρ u))) : G) = _
    rw [eσ.apply_symm_apply]
    rfl
  have htgt : σ (eρ u : G) 0 = (eD u.toAdd : Horizontal m) := by
    have h := translationEquiv_apply σ hσ (e u) 0
    change σ (eσ (e u) : G) 0 = 0 + ((e u).toAdd : Horizontal m) at h
    simpa [eD, he] using h
  rw [hsrc, hL, htgt]

theorem linear_intertwines (ρ σ : G →* (Horizontal m ≃ᵃⁱ[ℝ] Horizontal m))
    (hρ : Function.Injective ρ)
    (hker : (linearPart.comp ρ).ker ≤ (linearPart.comp σ).ker)
    [DiscreteTopology (translationModule ρ)] [IsZLattice ℝ (translationModule ρ)]
    (L : Horizontal m ≃L[ℝ] Horizontal m)
    (hL : ∀ t : (linearPart.comp ρ).ker, L (ρ (t : G) 0) = σ (t : G) 0)
    (g : G) (x : Horizontal m) :
    L ((ρ g).linearIsometryEquiv x) = (σ g).linearIsometryEquiv (L x) := by
  let A : Horizontal m →ₗ[ℝ] Horizontal m :=
    L.toLinearMap.comp (ρ g).linearIsometryEquiv.toLinearEquiv.toLinearMap
  let B : Horizontal m →ₗ[ℝ] Horizontal m :=
    (σ g).linearIsometryEquiv.toLinearEquiv.toLinearMap.comp L.toLinearMap
  have he : A = B := by
    apply LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := translationModule ρ))
    intro v hv
    let t := translationEquiv ρ hρ (Multiplicative.ofAdd (⟨v, hv⟩ : translationModule ρ))
    have ht : ρ (t : G) 0 = v := by
      simpa [t] using translationEquiv_apply ρ hρ
        (Multiplicative.ofAdd (⟨v, hv⟩ : translationModule ρ)) 0
    let c : (linearPart.comp ρ).ker :=
      ⟨g * (t : G) * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ t.property g⟩
    change L ((ρ g).linearIsometryEquiv v) = (σ g).linearIsometryEquiv (L v)
    rw [← ht, ← translationVector_conj ρ g t t.property, hL c,
      translationVector_conj σ g t (hker t.property), hL t]
  exact LinearMap.congr_fun he x

end LatticeExtension

def defectVector (ρ σ : G →* (E ≃ᵃⁱ[ℝ] E)) (L : E ≃L[ℝ] E) (g : G) : E :=
  σ g 0 - L (ρ g 0)

theorem defectVector_mul (ρ σ : G →* (E ≃ᵃⁱ[ℝ] E)) (L : E ≃L[ℝ] E)
    (hlin : ∀ g x, L ((ρ g).linearIsometryEquiv x) = (σ g).linearIsometryEquiv (L x))
    (g h : G) :
    defectVector ρ σ L (g * h) =
      (σ g).linearIsometryEquiv (defectVector ρ σ L h) + defectVector ρ σ L g := by
  simp only [defectVector, map_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply]
  rw [affine_eq_linear_add (σ g) (σ h 0), affine_eq_linear_add (ρ g) (ρ h 0),
    map_add, hlin, map_sub]
  abel

def defectAction (ρ σ : G →* (E ≃ᵃⁱ[ℝ] E)) (L : E ≃L[ℝ] E)
    (hlin : ∀ g x, L ((ρ g).linearIsometryEquiv x) = (σ g).linearIsometryEquiv (L x)) :
    G →* (E ≃ᵃⁱ[ℝ] E) where
  toFun g := AffineIsometryEquiv.mk'
    (fun x => (σ g).linearIsometryEquiv x + defectVector ρ σ L g)
      (σ g).linearIsometryEquiv 0 (by intro x; simp)
  map_one' := by
    ext x
    change (σ 1).linearIsometryEquiv x + (σ 1 0 - L (ρ 1 0)) = x
    rw [map_one, map_one]
    change x + (0 - L 0) = x
    rw [map_zero, sub_self, add_zero]
  map_mul' g h := by
    ext x
    change (σ (g * h)).linearIsometryEquiv x + defectVector ρ σ L (g * h) =
      (σ g).linearIsometryEquiv
        ((σ h).linearIsometryEquiv x + defectVector ρ σ L h) + defectVector ρ σ L g
    have he : (σ (g * h)).linearIsometryEquiv x =
        (σ g).linearIsometryEquiv ((σ h).linearIsometryEquiv x) := by
      rw [map_mul]
      rfl
    rw [he, defectVector_mul ρ σ L hlin, map_add, add_assoc]

theorem translation_kernel_le_defect_kernel (ρ σ : G →* (E ≃ᵃⁱ[ℝ] E))
    (L : E ≃L[ℝ] E)
    (hlin : ∀ g x, L ((ρ g).linearIsometryEquiv x) = (σ g).linearIsometryEquiv (L x))
    (hker : (linearPart.comp ρ).ker ≤ (linearPart.comp σ).ker)
    (hL : ∀ t : (linearPart.comp ρ).ker, L (ρ (t : G) 0) = σ (t : G) 0) :
    (linearPart.comp ρ).ker ≤ (defectAction ρ σ L hlin).ker := by
  intro g hg
  apply AffineIsometryEquiv.ext
  intro x
  change (σ g).linearIsometryEquiv x + (σ g 0 - L (ρ g 0)) = x
  have hA : linearPart (σ g) = 1 := hker hg
  have hx : (σ g).linearIsometryEquiv x = x :=
    congrArg (fun A : E ≃ₗᵢ[ℝ] E => A x) hA
  rw [hx, hL ⟨g, hg⟩, sub_self, add_zero]

theorem exists_fixed_point_of_finite_range (θ : G →* (E ≃ᵃⁱ[ℝ] E))
    [Finite θ.range] : ∃ b : E, ∀ g : G, θ g b = b := by
  classical
  let : Fintype θ.range := Fintype.ofFinite _
  let N : ℝ := Fintype.card θ.range
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let S : E := ∑ h : θ.range, (h : E ≃ᵃⁱ[ℝ] E) 0
  refine ⟨N⁻¹ • S, fun g => ?_⟩
  let a : θ.range := ⟨θ g, ⟨g, rfl⟩⟩
  have hperm : (∑ h : θ.range, θ g ((h : E ≃ᵃⁱ[ℝ] E) 0)) = S := by
    change (∑ h : θ.range, ((a * h : θ.range) : E ≃ᵃⁱ[ℝ] E) 0) = S
    exact Equiv.sum_comp (Equiv.mulLeft a) (fun h : θ.range => (h : E ≃ᵃⁱ[ℝ] E) 0)
  have hsum : (θ g).linearIsometryEquiv S + N • θ g 0 = S := by
    calc
      _ = ∑ h : θ.range, θ g ((h : E ≃ᵃⁱ[ℝ] E) 0) := by
        change (θ g).linearIsometryEquiv (∑ h : θ.range, (h : E ≃ᵃⁱ[ℝ] E) 0) +
            (Fintype.card θ.range : ℝ) • θ g 0 =
          ∑ h : θ.range, θ g ((h : E ≃ᵃⁱ[ℝ] E) 0)
        rw [show (∑ h : θ.range, θ g ((h : E ≃ᵃⁱ[ℝ] E) 0)) =
            ∑ h : θ.range, ((θ g).linearIsometryEquiv ((h : E ≃ᵃⁱ[ℝ] E) 0) + θ g 0) from
          Finset.sum_congr rfl (fun h _ => affine_eq_linear_add (θ g) _)]
        simp only [map_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Nat.cast_smul_eq_nsmul]
      _ = S := hperm
  rw [affine_eq_linear_add, map_smul]
  calc
    N⁻¹ • (θ g).linearIsometryEquiv S + θ g 0 =
        N⁻¹ • ((θ g).linearIsometryEquiv S + N • θ g 0) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hN, one_smul]
    _ = N⁻¹ • S := by rw [hsum]

theorem exists_affine_intertwiner_of_linear (ρ σ : G →* (E ≃ᵃⁱ[ℝ] E))
    [(linearPart.comp ρ).ker.FiniteIndex]
    (hker : (linearPart.comp ρ).ker ≤ (linearPart.comp σ).ker)
    (L : E ≃L[ℝ] E)
    (hL : ∀ t : (linearPart.comp ρ).ker, L (ρ (t : G) 0) = σ (t : G) 0)
    (hlin : ∀ g x, L ((ρ g).linearIsometryEquiv x) = (σ g).linearIsometryEquiv (L x)) :
    ∃ b : E, ∀ g x, L (ρ g x) + b = σ g (L x + b) := by
  let θ := defectAction ρ σ L hlin
  let : θ.ker.FiniteIndex := Subgroup.finiteIndex_of_le
    (translation_kernel_le_defect_kernel ρ σ L hlin hker hL)
  let : Finite θ.range := Finite.of_equiv (G ⧸ θ.ker) (QuotientGroup.quotientKerEquivRange θ)
  obtain ⟨b, hb⟩ := exists_fixed_point_of_finite_range θ
  refine ⟨b, fun g x => ?_⟩
  have he : (σ g).linearIsometryEquiv b + (σ g 0 - L (ρ g 0)) = b := hb g
  rw [affine_eq_linear_add (ρ g) x, map_add, hlin,
    affine_eq_linear_add (σ g) (L x + b), map_add]
  have he' : L (ρ g 0) + b = (σ g).linearIsometryEquiv b + σ g 0 := by
    calc
      _ = L (ρ g 0) + ((σ g).linearIsometryEquiv b + (σ g 0 - L (ρ g 0))) :=
        congrArg (L (ρ g 0) + ·) he.symm
      _ = _ := by abel
  rw [add_assoc, he', ← add_assoc]

theorem exists_affine_intertwiner {m : ℕ}
    (ρ σ : G →* (Horizontal m ≃ᵃⁱ[ℝ] Horizontal m))
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hcoρ : CoboundedOrbit ρ) (hcoσ : CoboundedOrbit σ)
    (hpρ : ∀ B : ℝ, {g : G | ‖ρ g 0‖ ≤ B}.Finite)
    (hpσ : ∀ B : ℝ, {g : G | ‖σ g 0‖ ≤ B}.Finite)
    (hvirt : Group.IsVirtuallyNilpotent G) :
    ∃ (L : Horizontal m ≃L[ℝ] Horizontal m) (b : Horizontal m),
      ∀ g x, L (ρ g x) + b = σ g (L x + b) := by
  let := discrete_translationModule ρ hpρ
  let := isZLattice_translationModule ρ hρ hcoρ hvirt
  let := finiteIndex_linear_kernel ρ hρ hcoρ hvirt
  have hker := (translation_kernel_eq ρ σ hρ hσ hcoρ hcoσ hvirt).le
  obtain ⟨L, hL⟩ := exists_linear_extension ρ σ hρ hσ hcoρ hcoσ hpρ hpσ hvirt
  obtain ⟨b, hb⟩ := exists_affine_intertwiner_of_linear ρ σ hker L hL
    (linear_intertwines ρ σ hρ hker L hL)
  exact ⟨L, b, hb⟩

end DifferentialGeometry.AffineCrystallographic
