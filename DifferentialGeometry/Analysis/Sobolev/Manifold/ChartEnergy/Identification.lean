import DifferentialGeometry.Analysis.Sobolev.Manifold.ChartEnergy.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Integrability
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence

section

noncomputable section

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {d m : ℕ}

theorem weakChartEnergyDensity_ae_eq_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : M → ℝ)
    {O : Set M} (hO : IsOpen O) (hOT : O ⊆ Φ.target) (hχ : ∀ p ∈ O, χ p = 1)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v U : EuclideanSpace ℝ (Fin d) → M}
    (hU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I 1 U Ω)
    (hvU : v =ᵐ[volume.restrict Ω] U)
    (hw : ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ (v x) • Φ.symm (v x)) k) Ω) :
    ∀ᵐ x ∂volume.restrict Ω, U x ∈ O →
      weakChartEnergyDensity g L Φ χ v hw x =
        (1 / 2 : ℝ) * ∑ j : Fin d, g.inner (U x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I U x (EuclideanSpace.single j 1))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I U x (EuclideanSpace.single j 1)) := by
  let S := Ω ∩ U ⁻¹' O
  have hS : IsOpen S := hU.continuousOn.isOpen_inter_preimage hΩ hO
  let X : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) :=
    fun x => L (Φ.symm (U x))
  have hX : ContDiffOn ℝ 1 X S :=
    L.contDiff.comp_contDiffOn
      (((Φ.contMDiffOn_invFun.of_le (by simp)).comp
        (hU.mono inter_subset_left) (fun _ hx => hOT hx.2)).contDiffOn)
  have heq (k : Fin m) :
      (fun x => L (χ (v x) • Φ.symm (v x)) k) =ᵐ[volume.restrict S]
        (fun x => X x k) := by
    filter_upwards [hvU.filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_left)),
      ae_restrict_mem hS.measurableSet] with x hx hxS
    rw [hx, hχ _ hxS.2, one_smul]
  let hs (k : Fin m) : DeGiorgi.MemW1pWitness 2 (fun x => X x k) S :=
    ((hw k).restrict hS inter_subset_left).congr (heq k)
  have hgrad (k : Fin m) := (hs k).weakGrad_ae_eq_smoothGradField (by norm_num) hS
    ((contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn hX)
  have hlocal : ∀ᵐ x ∂volume.restrict S,
      weakChartEnergyDensity g L Φ χ v hw x =
        (1 / 2 : ℝ) * ∑ j : Fin d, g.inner (U x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I U x (EuclideanSpace.single j 1))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I U x (EuclideanSpace.single j 1)) := by
    filter_upwards [ae_all_iff.mpr hgrad, ae_restrict_mem hS.measurableSet,
      hvU.filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_left))]
      with x hx hxS hvx
    have hdX : DifferentiableAt ℝ X x :=
      (hX.contDiffAt (hS.mem_nhds hxS)).differentiableAt one_ne_zero
    have hdU : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I U x :=
      (hU.contMDiffAt (hΩ.mem_nhds hxS.1)).mdifferentiableAt one_ne_zero
    have hcoord : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E)
        (Φ.symm ∘ U) x :=
      ((Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (hOT hxS.2))).mdifferentiableAt (by simp)).comp x hdU
    have hcols (j : Fin d) :
        WithLp.toLp 2 (fun k => (hw k).weakGrad x j) =
          fderiv ℝ X x (EuclideanSpace.single j 1) := by
      ext k
      have hh := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x hdX.hasFDerivAt
      change (hs k).weakGrad x j = (fderiv ℝ X x (EuclideanSpace.single j 1)) k
      rw [hx k]
      change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) k) ∘ X) x
        (EuclideanSpace.single j 1) = _
      rw [hh.fderiv]
      rfl
    have hL (j : Fin d) :
        L.symm (WithLp.toLp 2 (fun k => (hw k).weakGrad x j)) =
          fderiv ℝ (Φ.symm ∘ U) x (EuclideanSpace.single j 1) := by
      rw [hcols]
      have hh := L.hasFDerivAt.comp x hcoord.differentiableAt.hasFDerivAt
      change L.symm (fderiv ℝ (L ∘ (Φ.symm ∘ U)) x (EuclideanSpace.single j 1)) = _
      rw [hh.fderiv]
      exact L.symm_apply_apply _
    unfold weakChartEnergyDensity
    rw [hvx]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hL j]
    exact pullbackMetricCoefficients_fderiv_symm g Φ hdU (hOT hxS.2) _ _
  rw [ae_restrict_iff' hΩ.measurableSet]
  have hh := (ae_restrict_iff' hS.measurableSet).mp hlocal
  filter_upwards [hh] with x hx hxΩ hxO
  exact hx ⟨hxΩ, hxO⟩

theorem chartPartitionEnergyDensity_ae_eq_of_contMDiffOn
    {ι : Type*} [Countable ι]
    (g : SmoothRiemannianMetric I M) (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : ι → PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (χ : ι → M → ℝ)
    (ρ : PartitionOfUnity ι M univ)
    (hρ : ∀ i, tsupport (ρ i : M → ℝ) ⊆ interior {p | χ i p = 1} ∩ (Φ i).target)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v U : EuclideanSpace ℝ (Fin d) → M}
    (hU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I 1 U Ω)
    (hvU : v =ᵐ[volume.restrict Ω] U)
    (hw : ∀ i, ∀ k : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χ i (v x) • (Φ i).symm (v x)) k) Ω) :
    chartPartitionEnergyDensity g L Φ χ ρ v hw =ᵐ[volume.restrict Ω]
      (fun x => (1 / 2 : ℝ) * ∑ j : Fin d, g.inner (U x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I U x (EuclideanSpace.single j 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I U x (EuclideanSpace.single j 1))) := by
  have hi (i : ι) := weakChartEnergyDensity_ae_eq_of_contMDiffOn g L (Φ i) (χ i)
    (O := interior {p | χ i p = 1} ∩ (Φ i).target)
    (isOpen_interior.inter (Φ i).open_target) inter_subset_right
    (fun p hp => (interior_subset : interior {p : M | χ i p = 1} ⊆ _) hp.1)
    hΩ hU hvU (hw i)
  filter_upwards [ae_all_iff.mpr hi, hvU] with x hx hvx
  apply ρ.tsum_mul_eq_of_eq_on_support
  intro i hix
  apply hx i
  rw [← hvx]
  exact hρ i (subset_closure hix)

end DifferentialGeometry.Geometry

end

end
