import DifferentialGeometry.Topology.Handle.Extension
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import DifferentialGeometry.Topology.Embedding.LinearEquiv
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Embedding.AmbientIsotopy

section

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

private theorem isLocalDiffeomorphAt_of_bijective_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} (hF : ContDiff ℝ ∞ F) {x : E}
    (hx : Function.Bijective (fderiv ℝ F x)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F x := by
  let U : Set E := {z | IsUnit (fderiv ℝ F z)}
  have hU : IsOpen U := Units.isOpen.preimage (hF.continuous_fderiv (by simp))
  have hxU : x ∈ U := ContinuousLinearMap.isUnit_iff_bijective.mpr hx
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F U := by
    apply DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty hU
      hF.contMDiff.contMDiffOn
    intro z hz
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.id_comp,
      Function.comp_id, id_eq]
    obtain ⟨u, hu⟩ := hz
    refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
    rw [← hu]
    rfl
  exact hlocal ⟨x, hxU⟩

end DifferentialGeometry.Topology.Handle

end

section

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_native_closedCell_dilation (m : ℕ)
    {u : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ D : ℝ × ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡 (m + 1)) ∞ D ∧
      (∀ r (x y : ClosedCell (m + 1)), y.val = r • x.val → D (r, x) = u y) ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ (fun x => D (r, x)) := by
  obtain ⟨F, hF, _, hFu, hFd⟩ :=
    exists_contDiff_closedCell_extension_bijective_fderiv m hu.isImmersion
  let D : ℝ × ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun p => F (p.1 • p.2.val)
  have hD : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡 (m + 1)) ∞ D :=
    hF.comp_contMDiff (contMDiff_fst.smul
      ((closedCellInclusion_contMDiff m).comp contMDiff_snd))
  refine ⟨D, hD, ?_, ?_⟩
  · intro r x y hy
    change F (r • x.val) = u y
    rw [← hy, hFu]
  · intro r hr
    let S : ClosedCell (m + 1) → ClosedCell (m + 1) := fun x =>
      ⟨r • x.val, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
        exact (mul_le_mul_of_nonneg_right hr.2 (norm_nonneg x.val)).trans
          (by simpa only [one_mul] using x.property)⟩
    let e : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
      ContinuousLinearEquiv.smulLeft (Units.mk0 r hr.1.ne')
    have he := (closedCellInclusion_isSmoothEmbedding m).continuousLinearEquiv_comp e
    have hlocal : IsLocalDiffeomorphOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ F
        (Set.range (e ∘ (Subtype.val : ClosedCell (m + 1) →
          EuclideanSpace ℝ (Fin (m + 1))))) := by
      rintro ⟨z, x, rfl⟩
      exact isLocalDiffeomorphAt_of_bijective_fderiv hF (hFd (S x))
    have hi : Function.Injective (fun x : ClosedCell (m + 1) => D (r, x)) := by
      intro x y hxy
      have hs : S x = S y := hu.isEmbedding.injective (by
        rw [← hFu, ← hFu]
        exact hxy)
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val hs)
    have hDr : Continuous (fun x : ClosedCell (m + 1) => D (r, x)) :=
      (hD.comp (contMDiff_const.prodMk contMDiff_id)).continuous
    exact ⟨he.isImmersion.isLocalDiffeomorphOn_comp hlocal,
      (hDr.isClosedEmbedding hi).isEmbedding⟩

end DifferentialGeometry.Topology.Handle

end

section

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_compact_ambient_isotopy_closedCell_dilation (m : ℕ)
    {u : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u)
    {ρ : ℝ} (hρ : ρ ∈ Set.Ioc (0 : ℝ) 1)
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hU : IsOpen U) (huU : Set.range u ⊆ U) :
    ∃ Φ : ℝ → (EuclideanSpace ℝ (Fin (m + 1)) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin (m + 1))),
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl (𝓡 (m + 1)) (EuclideanSpace ℝ (Fin (m + 1))) ∞ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : ClosedCell (m + 1),
        y.val = (1 - t + t * ρ) • x.val →
          Φ t (u x) = u y ∧ (Φ t).symm (u y) = u x) ∧
      ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧ K ⊆ U ∧
        ∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ := by
  obtain ⟨D, hD, hread, hemb⟩ := exists_native_closedCell_dilation m hu
  let c : ℝ → ℝ := fun t => 1 - t + t * ρ
  have hc : ContDiff ℝ ∞ c := (contDiff_const.sub contDiff_id).add
    (contDiff_id.mul contDiff_const)
  have hcrange (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : c t ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp [c]
    constructor
    · nlinarith [hρ.1, mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hρ.2)]
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hρ.2)]
  let e : ℝ × ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun p => D (c p.1, p.2)
  have he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡 (m + 1)) ∞ e :=
    hD.comp ((hc.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hezero (x : ClosedCell (m + 1)) : e (0, x) = u x := by
    apply hread
    simp [c]
  have htrace : e '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ⊆ U := by
    rintro _ ⟨⟨t, x⟩, ht, rfl⟩
    have hr := hcrange t ht.1
    let y : ClosedCell (m + 1) := ⟨c t • x.val, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
      exact (mul_le_mul_of_nonneg_right hr.2 (norm_nonneg x.val)).trans
        (by simpa only [one_mul] using x.property)⟩
    have hy : e (t, x) = u y := hread (c t) x y rfl
    rw [hy]
    exact huU ⟨y, rfl⟩
  obtain ⟨Φ, hΦ, hΦi, hΦ0, hΦe, hK⟩ :=
    Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_Icc he.contMDiffOn
      (fun t ht => hemb (c t) (hcrange t ht)) hU htrace
  refine ⟨Φ, hΦ, hΦi, hΦ0, ?_, hK⟩
  intro t ht x y hy
  have hey : e (t, x) = u y := hread (c t) x y hy
  simpa only [hezero, hey] using hΦe t ht x

end DifferentialGeometry.Topology.Handle

end
