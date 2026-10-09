import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Hyperbolic.TruncationEnds
import DifferentialGeometry.Geometry.Hyperbolic.CuspVolume
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpace.Instances
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.ImmersionInterior

set_option autoImplicit false

noncomputable section

open Set Manifold GC.Endpoint
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

universe u

private theorem volume_image_cusp_tail_eq_intrinsic {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count) {a : ℝ} (ha : 0 ≤ a) :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (Tr.cuspMap i '' {p : CuspHalfSpace | a < p.2.val 0}) =
      Integral.Measure.riemannianVolumeMeasure halfCollarModel CuspHalfSpace
        (Tr.cusp i).metric {p | a < p.2.val 0} := by
  classical
  let Φ₀ : PartialDiffeomorph signedCollarModel halfCollarModel
      (Torus × ℝ) CuspHalfSpace ∞ :=
    Topology.PartialDiffeomorph.prod (Diffeomorph.refl torusModel Torus ∞).toPartialDiffeomorph
      Topology.Manifold.halfSpaceOneInteriorDiffeomorph
  let U : TopologicalSpace.Opens (Torus × ℝ) := ⟨Φ₀.source, Φ₀.open_source⟩
  let _ : LocallyCompactSpace U :=
    Manifold.locallyCompact_of_finiteDimensional signedCollarModel
  let f : U → CuspHalfSpace := fun x => Φ₀ x.val
  have hf : IsLocalDiffeomorph signedCollarModel halfCollarModel ∞ f :=
    isLocalDiffeomorph_restrict_open U (fun x => Φ₀.isLocalDiffeomorphAt _ _ _ x.property)
  have hfinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Φ₀.toPartialEquiv.injOn x.property y.property hxy)
  let _ : Nonempty U := ⟨⟨((1, 1), 1), by
    change ((1, 1) : Torus) ∈ (univ : Set Torus) ∧ (1 : ℝ) ∈ Ioi 0
    exact ⟨mem_univ _, by norm_num⟩⟩⟩
  let g : SmoothRiemannianMetric signedCollarModel U :=
    localPullMetric (Tr.cusp i).metric f hf
  let k : U → H.Carrier := Tr.cuspMap i ∘ f
  have hc : ContMDiff halfCollarModel (𝓡 3) ∞ (Tr.cuspMap i) :=
    (Tr.cuspEmbedding i).contMDiff
  have hk : ContMDiff signedCollarModel (𝓡 3) ∞ k := hc.comp hf.contMDiff
  have hkD (x : U) :
      mfderiv signedCollarModel (𝓡 3) k x =
        (mfderiv halfCollarModel (𝓡 3) (Tr.cuspMap i) (f x)).comp
          (mfderiv signedCollarModel halfCollarModel f x) :=
    mfderiv_comp x (hc.mdifferentiableAt (by simp))
      (hf.contMDiff.mdifferentiableAt (by simp))
  have hk_local : IsLocalDiffeomorph signedCollarModel (𝓡 3) ∞ k := by
    intro x
    apply Topology.Manifold.isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
      hk BoundarylessManifold.isInteriorPoint (by simp)
    rw [hkD]
    exact ((Tr.cuspEmbedding i).isImmersion.mfderiv_injective (by simp) (f x)).comp
      ((hf x).mfderivToContinuousLinearEquiv (by simp)).injective
  have hkinj : Function.Injective k := (Tr.cuspEmbedding i).isEmbedding.injective.comp hfinj
  obtain ⟨Φ, hΦs, _, hΦf⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      (hf.isLocalDiffeomorphOn univ)
      isOpen_univ (Set.univ_nonempty) hfinj.injOn
  obtain ⟨Ψ, hΨs, _, hΨf⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      (hk_local.isLocalDiffeomorphOn univ)
      isOpen_univ (Set.univ_nonempty) hkinj.injOn
  let Φ₁ : PartialDiffeomorph signedCollarModel halfCollarModel U CuspHalfSpace 1 :=
    { Φ with
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  let Ψ₁ : PartialDiffeomorph signedCollarModel (𝓡 3) U H.Carrier 1 :=
    { Ψ with
      contMDiffOn_toFun := Ψ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Ψ.contMDiffOn_invFun.of_le (by norm_num) }
  have hΦcoe : (Φ₁ : U → CuspHalfSpace) = f := hΦf
  have hΨcoe : (Ψ₁ : U → H.Carrier) = k := hΨf
  have hmetricΦ : ∀ x ∈ Φ₁.source, ∀ v w, g.inner x v w =
      (Tr.cusp i).metric.inner (Φ₁ x)
        (mfderiv signedCollarModel halfCollarModel Φ₁ x v)
        (mfderiv signedCollarModel halfCollarModel Φ₁ x w) := by
    intro x _ v w
    rw [hΦcoe]
    exact localPullMetric_inner (Tr.cusp i).metric f hf x v w
  have hmetricΨ : ∀ x ∈ Ψ₁.source, ∀ v w, g.inner x v w =
      H.metric.inner (Ψ₁ x)
        (mfderiv signedCollarModel (𝓡 3) Ψ₁ x v)
        (mfderiv signedCollarModel (𝓡 3) Ψ₁ x w) := by
    intro x _ v w
    rw [hΨcoe, hkD, localPullMetric_inner]
    exact (Tr.cuspIsometry i (f x) _ _).symm
  let A : Set U := f ⁻¹' {p : CuspHalfSpace | a < p.2.val 0}
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := ⟨rfl⟩
  have hA : MeasurableSet A := by
    apply IsOpen.measurableSet
    exact (isOpen_lt continuous_const
      ((EuclideanSpace.proj 0).continuous.comp
        (continuous_subtype_val.comp continuous_snd))).preimage hf.contMDiff.continuous
  have hfA : f '' A = {p : CuspHalfSpace | a < p.2.val 0} := by
    apply image_preimage_eq_of_subset
    intro p hp
    have hpT : p ∈ Φ₀.target := by
      change p.1 ∈ (univ : Set Torus) ∧ 0 < p.2.val 0
      exact ⟨mem_univ _, lt_of_le_of_lt ha hp⟩
    exact ⟨⟨Φ₀.symm p, Φ₀.map_target hpT⟩, Φ₀.right_inv' hpT⟩
  have hvolΦ := Integral.Measure.riemannianVolumeMeasure_image_of_partialIsometry
    g (Tr.cusp i).metric Φ₁ hmetricΦ hA (by simpa only [show Φ₁.source = univ from hΦs]
      using (subset_univ A))
  have hvolΨ := Integral.Measure.riemannianVolumeMeasure_image_of_partialIsometry
    g H.metric Ψ₁ hmetricΨ hA (by simpa only [show Ψ₁.source = univ from hΨs]
      using (subset_univ A))
  rw [hΦcoe, hfA] at hvolΦ
  rw [hΨcoe, show k = Tr.cuspMap i ∘ f from rfl, image_comp, hfA] at hvolΨ
  exact hvolΨ.symm.trans hvolΦ

theorem volume_image_cusp_tail {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count) {a : ℝ} (ha : 0 ≤ a) :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (Tr.cuspMap i '' {p : CuspHalfSpace | a < p.2.val 0}) =
      Integral.Measure.riemannianVolumeMeasure torusModel Torus
        (Tr.cusp i).torusMetric univ * ENNReal.ofReal (Real.exp (-a)) :=
  (volume_image_cusp_tail_eq_intrinsic Tr i ha).trans ((Tr.cusp i).volume_tail ha)


theorem volume_iUnion_cusp_tail {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (a : Fin Tr.count → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (⋃ i, Tr.cuspMap i '' {p : CuspHalfSpace | a i < p.2.val 0}) =
      ∑ i, Integral.Measure.riemannianVolumeMeasure torusModel Torus
        (Tr.cusp i).torusMetric univ * ENNReal.ofReal (Real.exp (-a i)) := by
  classical
  let _ : MeasurableSpace H.Carrier := borel H.Carrier
  let _ : BorelSpace H.Carrier := ⟨rfl⟩
  let _ : MeasurableSpace CuspHalfSpace := borel CuspHalfSpace
  let _ : BorelSpace CuspHalfSpace := ⟨rfl⟩
  have hmeas (i : Fin Tr.count) :
      MeasurableSet (Tr.cuspMap i '' {p : CuspHalfSpace | a i < p.2.val 0}) := by
    apply (Tr.cuspMap_isClosedEmbedding i).measurableEmbedding.measurableSet_image.mpr
    apply IsOpen.measurableSet
    exact isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd))
  have hdisjoint : Pairwise (fun i j => Disjoint
      (Tr.cuspMap i '' {p : CuspHalfSpace | a i < p.2.val 0})
      (Tr.cuspMap j '' {p : CuspHalfSpace | a j < p.2.val 0})) := by
    intro i j hij
    exact (Tr.cusp_disjoint hij).mono (image_subset_range _ _) (image_subset_range _ _)
  rw [MeasureTheory.measure_iUnion hdisjoint hmeas, tsum_fintype]
  exact Finset.sum_congr rfl (fun i _ => Tr.volume_image_cusp_tail i (ha i))

theorem volume_compl_range_inclusion {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (range Tr.inclusion)ᶜ =
      ∑ i, Integral.Measure.riemannianVolumeMeasure torusModel Torus
        (Tr.cusp i).torusMetric univ := by
  have hcomplement : (range Tr.inclusion)ᶜ =
      ⋃ i, Tr.cuspMap i '' {p : CuspHalfSpace | 0 < p.2.val 0} := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ range Tr.inclusion ∪ ⋃ i, range (Tr.cuspMap i) := by
        rw [Tr.exhausts]
        exact mem_univ x
      rcases hx' with hcore | htail
      · exact False.elim (hx hcore)
      · obtain ⟨i, p, rfl⟩ := mem_iUnion.mp htail
        by_cases hp : 0 < p.2.val 0
        · exact mem_iUnion.mpr ⟨i, p, hp, rfl⟩
        · have hp0 : p.2 = halfZero := by
            apply Topology.Manifold.halfSpaceOneHomeomorph.injective
            exact Subtype.ext (le_antisymm (le_of_not_gt hp) p.2.property)
          apply False.elim (hx ?_)
          exact ⟨Tr.boundary.torusMap i p.1, by rw [← Tr.cusp_zero, ← hp0]⟩
    · intro hx
      obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
      intro hcore
      have hint : Tr.cuspMap i p ∈ range Tr.inclusion ∩ range (Tr.cuspMap i) :=
        ⟨hcore, mem_range_self p⟩
      rw [Tr.intersection i] at hint
      obtain ⟨t, ht⟩ := hint
      have heq := (Tr.cuspEmbedding i).isEmbedding.injective ht
      have hz : p.2.val 0 = 0 := by
        rw [← heq]
        rfl
      exact hp.ne' hz
  rw [hcomplement]
  simpa using Tr.volume_iUnion_cusp_tail (fun _ => 0) (fun _ => le_rfl)

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
