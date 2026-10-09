import DifferentialGeometry.Geometry.Metric.ExteriorPower
import DifferentialGeometry.Tensor.Alternating.Contraction
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false

noncomputable section

open scoped RealInnerProductSpace

namespace exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem musicalEquiv_map_subtype (k : ℕ) (P : Submodule ℝ E)
    (u : ⋀[ℝ]^k P) :
    musicalEquiv k (map k P.subtype u) =
      (musicalEquiv k u).compContinuousLinearMap P.orthogonalProjectionOnto := by
  have h : (musicalEquiv k (E := E)).toLinearMap.comp (map k P.subtype) =
      (ContinuousAlternatingMap.compContinuousLinearMapₗ P.orthogonalProjectionOnto).comp
        (musicalEquiv k (E := P)).toLinearMap := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply ContinuousAlternatingMap.ext
    intro w
    change musicalEquiv k (map k P.subtype (ιMulti ℝ k v)) w =
      ((musicalEquiv k (ιMulti ℝ k v)).compContinuousLinearMap
        P.orthogonalProjectionOnto) w
    rw [map_apply_ιMulti, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      musicalEquiv_ιMulti_apply, musicalEquiv_ιMulti_apply]
    congr 1
    funext i j
    exact (P.inner_orthogonalProjectionOnto_eq_of_mem_left (v j) (w i)).symm
  exact LinearMap.congr_fun h u

end exteriorPower

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem comp_starProjection_eq_of_le_contractionAnnihilator
    (K : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ))
    (L : Submodule ℝ E) [L.HasOrthogonalProjection]
    (hL : L ≤ contractionAnnihilator K)
    {ω : E [⋀^Fin 2]→L[ℝ] ℝ} (hω : ω ∈ K) :
    ω.compContinuousLinearMap Lᗮ.starProjection = ω := by
  have hleft (u v : E) : ω ![L.starProjection u, v] = 0 := by
    have h := (mem_contractionAnnihilator_iff.mp
      (hL (L.orthogonalProjectionOnto u).property)) ω hω
    exact congrArg (fun α : E [⋀^Fin 1]→L[ℝ] ℝ => α ![v]) h
  ext v
  have hvec : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec, compContinuousLinearMap_apply]
  have hcomp : (⇑Lᗮ.starProjection ∘ ![v 0, v 1]) =
      ![Lᗮ.starProjection (v 0), Lᗮ.starProjection (v 1)] := by
    ext i
    fin_cases i <;> rfl
  rw [hcomp]
  rw [L.starProjection_orthogonal]
  change ω ![v 0 - L.starProjection (v 0), v 1 - L.starProjection (v 1)] = _
  rw [ω.map_vecCons_sub]
  have hsecond : ω ![v 0, v 1 - L.starProjection (v 1)] = ω ![v 0, v 1] := by
    have hswap (a b : E) : ω ![a, b] = -ω ![b, a] := by
      simpa using ω.map_swap (v := ![b, a]) (i := (0 : Fin 2)) (j := 1) (by decide)
    rw [hswap, ω.map_vecCons_sub, hleft, sub_zero, hswap]
    exact neg_neg _
  rw [hsecond, hleft, sub_zero]

theorem eq_musicalEquiv_map_orthogonal_contractionAnnihilator_of_finrank_eq_one
    (hE : Module.finrank ℝ E = 3)
    (K : Submodule ℝ (E [⋀^Fin 2]→L[ℝ] ℝ))
    (hK : Module.finrank ℝ K = 1) :
    K = LinearMap.range
      ((exteriorPower.musicalEquiv 2 (E := E)).toLinearMap.comp
        (exteriorPower.map 2 (contractionAnnihilator K)ᗮ.subtype)) := by
  let L := contractionAnnihilator K
  let P := Lᗮ
  let F := (exteriorPower.musicalEquiv 2 (E := E)).toLinearMap.comp
    (exteriorPower.map 2 P.subtype)
  have hP : Module.finrank ℝ P = 2 := by
    have hsum := L.finrank_add_finrank_orthogonal
    have hL := finrank_contractionAnnihilator_eq_one hE K hK
    change Module.finrank ℝ L = 1 at hL
    rw [hE, hL] at hsum
    change 1 + Module.finrank ℝ P = 3 at hsum
    omega
  apply Submodule.eq_of_le_of_finrank_le
  · intro ω hω
    let α := ω.compContinuousLinearMap P.subtypeL
    refine ⟨(exteriorPower.musicalEquiv 2 (E := P)).symm α, ?_⟩
    change exteriorPower.musicalEquiv 2
      (exteriorPower.map 2 P.subtype
        ((exteriorPower.musicalEquiv 2 (E := P)).symm α)) = ω
    rw [exteriorPower.musicalEquiv_map_subtype, ContinuousLinearEquiv.apply_symm_apply]
    have heq : α.compContinuousLinearMap P.orthogonalProjectionOnto =
        ω.compContinuousLinearMap P.starProjection := by
      ext v
      rfl
    rw [heq]
    exact comp_starProjection_eq_of_le_contractionAnnihilator K L le_rfl hω
  · have hdim : Module.finrank ℝ (⋀[ℝ]^2 P) = 1 := by
      rw [exteriorPower.finrank_eq, hP]
      rfl
    have hle := F.finrank_range_le
    rw [hdim, ← hK] at hle
    exact hle

end ContinuousAlternatingMap
