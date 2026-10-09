import DifferentialGeometry.Geometry.Submanifold.NormalBundle.UnitNormal
import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.LinearAlgebra.CrossProduct

/-!
# S-W-STAB-2 G2b：浸入曲面沿一点邻域的光滑 transverse 场（局部叉积构造）

`U : ℂ → M` 在开集 `s` 上光滑且 `mfderiv` 单射，`M` 是三维流形。取 `z₀ ∈ s`、`p = U z₀` 处的切丛平凡化
`t`。`α(z) = t(dU_z 1)`、`β(z) = t(dU_z i)`（`E`-值光滑函数），基 `B₀` 下坐标的叉积 `α × β` 给出
`w : ℂ → E`，`V z := t.symmL (w z)`。`V` 在 `s ∩ U⁻¹(t.baseSet)` 上光滑，且 `V z ∉ range dU_z`
（`c·c = c·(xa + yb) = 0`）。然后用 `exists_contMDiff_unit_normal_of_transverse` 得到局部单位法向。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Matrix
open scoped ContDiff Manifold _root_.Topology

namespace DifferentialGeometry.Geometry

theorem cross_not_mem_span_WS2 {a b : Fin 3 → ℝ} (hab : LinearIndependent ℝ ![a, b]) (x y : ℝ) :
    crossProduct a b ≠ x • a + y • b := by
  intro h
  have h1 : crossProduct a b ⬝ᵥ crossProduct a b = 0 := by
    have : crossProduct a b ⬝ᵥ crossProduct a b = crossProduct a b ⬝ᵥ (x • a + y • b) := by
      rw [← h]
    rw [this, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm _ a,
      dotProduct_comm _ b, dot_self_cross, dot_cross_self]
    simp
  exact (crossProduct_ne_zero_iff_linearIndependent.mpr hab) (dotProduct_self_eq_zero.mp h1)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **局部 transverse 场.**  `U` 在开集 `s` 上光滑、`mfderiv` 单射，`dim E = 3`：对 `z₀ ∈ s`
存在 `z₀` 的开邻域 `s₀ ⊆ s` 与沿 `U` 的光滑切向场 `V`，在 `s₀` 上光滑且不在 `range dU` 里。 -/
theorem exists_local_transverse_WS2 (hdim : Module.finrank ℝ E = 3) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hinj : ∀ z ∈ s, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ s) :
    ∃ s₀ : Set ℂ, IsOpen s₀ ∧ z₀ ∈ s₀ ∧ s₀ ⊆ s ∧
      ∃ V : ∀ z : ℂ, TangentSpace 𝓘(ℝ, E) (U z),
        ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
          (fun z => (⟨U z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) s₀ ∧
        ∀ z ∈ s₀, V z ∉ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z).range := by
  let p : M := U z₀
  let t : Trivialization E (π E (TangentSpace 𝓘(ℝ, E))) :=
    trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  let s₀ : Set ℂ := s ∩ U ⁻¹' t.baseSet
  have hs₀ : IsOpen s₀ := hU.continuousOn.isOpen_inter_preimage hs t.open_baseSet
  have hp : p ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hz₀' : z₀ ∈ s₀ := ⟨hz₀, hp⟩
  have hmaps : ∀ (v : ℂ), MapsTo (fun z => (TotalSpace.mk' E (U z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) : TotalSpace E (TangentSpace 𝓘(ℝ, E)))) s₀ t.source :=
    fun v z hz => t.mem_source.mpr hz.2
  have hcoord : ∀ v : ℂ, ContDiffOn ℝ ∞
      (fun z => (t (TotalSpace.mk' E (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) :
        TotalSpace E (TangentSpace 𝓘(ℝ, E)))).2) s₀ := by
    intro v
    have h1 := contMDiffOn_source_partial (m := ∞) (n := ∞) hs hU (by simp) v
    have h2 := ((Trivialization.contMDiffOn_iff (hmaps v)).mp (h1.mono inter_subset_left)).2
    exact contMDiffOn_iff_contDiffOn.mp h2
  let α : ℂ → E := fun z =>
    (t (TotalSpace.mk' E (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ)) :
      TotalSpace E (TangentSpace 𝓘(ℝ, E)))).2
  let β : ℂ → E := fun z =>
    (t (TotalSpace.mk' E (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I) :
      TotalSpace E (TangentSpace 𝓘(ℝ, E)))).2
  have hα : ContDiffOn ℝ ∞ α s₀ := hcoord 1
  have hβ : ContDiffOn ℝ ∞ β s₀ := hcoord Complex.I
  let B₀ : Module.Basis (Fin 3) ℝ E := (Module.finBasis ℝ E).reindex (finCongr hdim)
  let Q : E →L[ℝ] (Fin 3 → ℝ) := LinearMap.toContinuousLinearMap B₀.equivFun.toLinearMap
  let Q' : (Fin 3 → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap B₀.equivFun.symm.toLinearMap
  have hQQ' : ∀ x : Fin 3 → ℝ, Q (Q' x) = x := fun x => B₀.equivFun.apply_symm_apply x
  let c : ℂ → (Fin 3 → ℝ) := fun z => crossProduct (Q (α z)) (Q (β z))
  have hA : ∀ i, ContDiffOn ℝ ∞ (fun z => Q (α z) i) s₀ :=
    fun i => (contDiff_apply ℝ ℝ i).comp_contDiffOn (Q.contDiff.comp_contDiffOn hα)
  have hB : ∀ i, ContDiffOn ℝ ∞ (fun z => Q (β z) i) s₀ :=
    fun i => (contDiff_apply ℝ ℝ i).comp_contDiffOn (Q.contDiff.comp_contDiffOn hβ)
  have hc : ContDiffOn ℝ ∞ c s₀ := by
    rw [contDiffOn_pi]
    intro k
    fin_cases k
    · simpa [c, cross_apply] using ((hA 1).mul (hB 2)).sub ((hA 2).mul (hB 1))
    · simpa [c, cross_apply] using ((hA 2).mul (hB 0)).sub ((hA 0).mul (hB 2))
    · simpa [c, cross_apply] using ((hA 0).mul (hB 1)).sub ((hA 1).mul (hB 0))
  let w : ℂ → E := fun z => Q' (c z)
  have hw : ContDiffOn ℝ ∞ w s₀ := Q'.contDiff.comp_contDiffOn hc
  refine ⟨s₀, hs₀, hz₀', inter_subset_left, fun z => t.symmL ℝ (U z) (w z), ?_, ?_⟩
  · have hmapsV : MapsTo (fun z => (TotalSpace.mk' E (U z) (t.symmL ℝ (U z) (w z)) :
        TotalSpace E (TangentSpace 𝓘(ℝ, E)))) s₀ t.source :=
      fun z hz => t.mem_source.mpr hz.2
    have hUs₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s₀ := hU.mono inter_subset_left
    refine (Trivialization.contMDiffOn_iff hmapsV).mpr ⟨hUs₀, ?_⟩
    refine (contMDiffOn_iff_contDiffOn.mpr hw).congr ?_
    intro z hz
    have h1 := t.apply_mk_symm hz.2 (w z)
    rw [← t.symmL_apply (R := ℝ) hz.2 (w z)] at h1
    exact congrArg Prod.snd h1
  · intro z hz hmem
    let L : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U z) := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
    have hLinj : Function.Injective L := hinj z hz.1
    obtain ⟨v, hv⟩ : ∃ v : ℂ, L v = t.symmL ℝ (U z) (w z) := hmem
    have hzb : U z ∈ t.baseSet := hz.2
    let T₀ := t.continuousLinearEquivAt ℝ (U z) hzb
    have hsymm : t.symmL ℝ (U z) (w z) = T₀.symm (w z) := by
      have h := t.symm_continuousLinearEquivAt_eq' (R := ℝ) hzb
      rw [← h]
      rfl
    have hdec : L v = v.re • L (1 : ℂ) + v.im • L Complex.I := by
      have hv' : v = v.re • (1 : ℂ) + v.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      conv_lhs => rw [hv']
      rw [map_add, map_smul, map_smul]
    have hwz : w z = v.re • α z + v.im • β z := by
      have h1 : T₀ (L v) = w z := by
        rw [hv, hsymm, T₀.apply_symm_apply]
      rw [← h1, hdec, map_add, map_smul, map_smul]
      rfl
    have hcz : crossProduct (Q (α z)) (Q (β z)) = v.re • Q (α z) + v.im • Q (β z) := by
      have h1 : Q (w z) = c z := hQQ' (c z)
      rw [← map_smul, ← map_smul, ← map_add, ← hwz]
      exact h1.symm
    have hindep : LinearIndependent ℝ ![Q (α z), Q (β z)] := by
      rw [LinearIndependent.pair_iff]
      intro x y hxy
      have hQinj : Function.Injective Q := B₀.equivFun.injective
      have h0 : x • α z + y • β z = 0 := by
        apply hQinj
        rw [map_add, map_smul, map_smul, map_zero]
        exact hxy
      have h1 : T₀ (L (x • (1 : ℂ) + y • Complex.I)) = 0 := by
        rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
        exact h0
      have h2 : L (x • (1 : ℂ) + y • Complex.I) = 0 :=
        T₀.injective (by rw [h1, map_zero])
      have h3 : x • (1 : ℂ) + y • Complex.I = 0 :=
        hLinj (by rw [h2, map_zero])
      exact ⟨by simpa [Complex.real_smul] using congrArg Complex.re h3,
        by simpa [Complex.real_smul] using congrArg Complex.im h3⟩
    exact cross_not_mem_span_WS2 hindep v.re v.im hcz

/-- **局部光滑单位法向.**  `U` 在开集 `s` 上光滑、`mfderiv` 单射、`dim E = 3`：对 `z₀ ∈ s`
存在 `z₀` 的开邻域 `s₀ ⊆ s` 与沿 `U` 的光滑单位法向场 `ν`（`ν` 对一切 `z : ℂ` 都有定义，
只在 `s₀` 上有意义）。 -/
theorem exists_local_unit_normal_WS2 (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hinj : ∀ z ∈ s, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ s) :
    ∃ s₀ : Set ℂ, IsOpen s₀ ∧ z₀ ∈ s₀ ∧ s₀ ⊆ s ∧
      ∃ ν : ∀ z : ℂ, TangentSpace 𝓘(ℝ, E) (U z),
        ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
          (fun z => (⟨U z, ν z⟩ : TangentBundle 𝓘(ℝ, E) M)) s₀ ∧
        (∀ z ∈ s₀, g.inner (U z) (ν z) (ν z) = 1) ∧
        ∀ z ∈ s₀, ∀ v : ℂ,
          g.inner (U z) (ν z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) = 0 := by
  classical
  obtain ⟨s₀, hs₀, hz₀', hss, V, hVsm, hVtr⟩ := exists_local_transverse_WS2 hdim hs hU hinj hz₀
  let S₀ : TopologicalSpace.Opens ℂ := ⟨s₀, hs₀⟩
  have hUs₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s₀ := hU.mono hss
  have hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : S₀ => U q) :=
    fun q => contMDiffAt_subtype_iff.mpr (hUs₀.contMDiffAt (hs₀.mem_nhds q.2))
  have hdf : ∀ q : S₀, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : S₀ => U p) q =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
    fun q => DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U S₀ q
  have hinj' : ∀ q : S₀, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : S₀ => U p) q) := by
    intro q
    rw [hdf q]
    exact hinj q (hss q.2)
  have hV' : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : S₀ => (⟨U q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    fun q => contMDiffAt_subtype_iff.mpr (hVsm.contMDiffAt (hs₀.mem_nhds q.2))
  have htr' : ∀ q : S₀, V q ∉ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : S₀ => U p) q).range := by
    intro q
    rw [hdf q]
    exact hVtr q q.2
  obtain ⟨ν', hν'sm, hν'unit, hν'nor⟩ :=
    exists_contMDiff_unit_normal_of_transverse g hf hinj' (fun q : S₀ => V q) hV' htr'
  let ν : ∀ z : ℂ, TangentSpace 𝓘(ℝ, E) (U z) :=
    fun z => if h : z ∈ s₀ then ν' ⟨z, h⟩ else 0
  have hν : ∀ (z : ℂ) (h : z ∈ s₀), ν z = ν' ⟨z, h⟩ := fun z h => by simp [ν, h]
  refine ⟨s₀, hs₀, hz₀', hss, ν, ?_, ?_, ?_⟩
  · intro z hz
    have h1 : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
        (fun q : S₀ => (⟨U q, ν' q⟩ : TangentBundle 𝓘(ℝ, E) M)) ⟨z, hz⟩ := hν'sm ⟨z, hz⟩
    have h2 := (contMDiffAt_subtype_iff (U := S₀)
      (f := fun z : ℂ => (⟨U z, ν z⟩ : TangentBundle 𝓘(ℝ, E) M)) (x := ⟨z, hz⟩)).mp
      (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by
        change (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M) = ⟨U q, ν' q⟩
        rw [hν q q.2]))
    exact h2.contMDiffWithinAt
  · intro z hz
    rw [hν z hz]
    exact hν'unit ⟨z, hz⟩
  · intro z hz v
    rw [hν z hz, ← hdf ⟨z, hz⟩]
    exact hν'nor ⟨z, hz⟩ v

end DifferentialGeometry.Geometry
