import DifferentialGeometry.Topology.VectorField.Index
import DifferentialGeometry.Topology.LocalDegree.Determinant

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField

variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]

theorem fderiv_mpullback_eq_linearizationAtZero {n : ℕ∞ω}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M n) (hn : 2 ≤ n)
    {V : ∀ x : M, TangentSpace I x} {a : EuclideanSpace ℝ (Fin (d + 1))}
    (ha : a ∈ f.source)
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) (f a))
    (hz : V (f a) = 0) :
    fderiv ℝ (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a =
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f a).inverse ∘L
        linearizationAtZero hV hz ∘L
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f a := by
  have hh := linearizationAtZero_mpullback_partialDiffeomorph f hn ha hV hz
  rw [linearizationAtZero_eq_fderivWithin] at hh
  simp only [mfld_simps, chartAt_self_eq] at hh
  change fderivWithin ℝ
    (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V :
      EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))) univ a = _ at hh
  erw [fderivWithin_univ] at hh
  exact hh

theorem det_fderiv_mpullback_eq_linearizationAtZero {n : ℕ∞ω}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M n) (hn : 2 ≤ n)
    {V : ∀ x : M, TangentSpace I x} {a : EuclideanSpace ℝ (Fin (d + 1))}
    (ha : a ∈ f.source)
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) (f a))
    (hz : V (f a) = 0) :
    LinearMap.det (fderiv ℝ
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a).toLinearMap =
      LinearMap.det (linearizationAtZero hV hz).toLinearMap := by
  rw [fderiv_mpullback_eq_linearizationAtZero I f hn ha hV hz]
  obtain ⟨e, he⟩ := isInvertible_mfderiv_partialDiffeomorph f
    (ne_of_gt (lt_of_lt_of_le (by norm_num) hn)) ha
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact LinearMap.det_conj (linearizationAtZero hV hz).toLinearMap e.symm.toLinearEquiv

theorem differentiableAt_mpullback_in_model {n : ℕ∞ω}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M n) (hn : 2 ≤ n)
    {V : ∀ x : M, TangentSpace I x} {a : EuclideanSpace ℝ (Fin (d + 1))}
    (ha : a ∈ f.source)
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) (f a)) :
    DifferentiableAt ℝ
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a := by
  have hh := mdifferentiableAt_mpullback_partialDiffeomorph f hn ha hV
  rw [mdifferentiableAt_section] at hh
  simp only [trivializationAt_model_space_apply] at hh
  change MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1)))
    (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a at hh
  exact mdifferentiableAt_iff_differentiableAt.mp hh

theorem hasContinuousIsolatedZero_of_det_linearizationAtZero_ne_zero_in_model {n : ℕ∞ω}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M n) (hn : 2 ≤ n)
    {V : ∀ x : M, TangentSpace I x} {a : EuclideanSpace ℝ (Fin (d + 1))}
    (ha : a ∈ f.source)
    (hc : ∃ s ∈ 𝓝 (f a), ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I M)) s)
    (hd : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) (f a))
    (hz : V (f a) = 0)
    (hdet : LinearMap.det (linearizationAtZero hd hz).toLinearMap ≠ 0) :
    HasContinuousIsolatedZero I V (f a) := by
  obtain ⟨s, hs, hcs⟩ := hc
  obtain ⟨U, hUs, hU, haU⟩ := mem_nhds_iff.mp hs
  let t := f.source ∩ f ⁻¹' U
  have ht : t ∈ 𝓝 a := inter_mem (f.open_source.mem_nhds ha)
    ((f.toOpenPartialHomeomorph.continuousAt ha).preimage_mem_nhds (hU.mem_nhds haU))
  have hP : ContinuousOn
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) t := by
    intro y hy
    have hVy : ContMDiffAt I I.tangent 0
        (fun z => (⟨z, V z⟩ : TangentBundle I M)) (f y) :=
      (contMDiffOn_zero_iff.mpr (hcs.mono hUs)).contMDiffAt (hU.mem_nhds hy.2)
    have hgraph := (contMDiffAt_mpullback_partialDiffeomorph f
      (m := 0) (by simpa using (show 1 ≤ n from (by norm_num : 1 ≤ (2 : ℕ∞ω)).trans hn))
      hy.1 hVy).continuousAt.continuousWithinAt (s := t)
    have hcomp := (FiberBundle.continuousWithinAt_section
      (EuclideanSpace ℝ (Fin (d + 1)))).mp hgraph
    simpa only [trivializationAt_model_space_apply] using! hcomp
  have hD := differentiableAt_mpullback_in_model I f hn ha hd
  have hdetEq := det_fderiv_mpullback_eq_linearizationAtZero I f hn ha hd hz
  have hDdet : LinearMap.det (fderiv ℝ
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a).toLinearMap ≠ 0 :=
    hdetEq ▸ hdet
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
  have hPz := (mpullback_partialDiffeomorph_eq_zero_iff f hn0 V ha).mpr hz
  have hPi := Poincare.LocalDegree.isolatedZero_of_det_fderiv_ne_zero ht hP hPz hD hDdet
  have hiso : ∀ᶠ y in 𝓝 a,
      _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V y = 0 → y = a := by
    filter_upwards [Metric.closedBall_mem_nhds a hPi.choose_spec.pos] with y hy
    exact (hPi.choose_spec.zero_iff y hy).mp
  exact ⟨hz, ⟨s, hs, hcs⟩, (mpullback_partialDiffeomorph_isolated_iff f hn0 V ha).mp hiso⟩

variable [I.Boundaryless]

theorem index_eq_sign_det_linearizationAtZero_in_model {n : ℕ∞ω}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M n) (hn : 2 ≤ n)
    {V : ∀ x : M, TangentSpace I x} {a : EuclideanSpace ℝ (Fin (d + 1))}
    (ha : a ∈ f.source) (hV : HasContinuousIsolatedZero I V (f a))
    (hd : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) (f a))
    (hdet : LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap ≠ 0) :
    index I V (f a) hV =
      (SignType.sign (LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap) : ℤ) := by
  let f₁ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M 1 :=
    { f with
      contMDiffOn_toFun := f.contMDiffOn_toFun.of_le ((by norm_num : 1 ≤ (2 : ℕ∞ω)).trans hn)
      contMDiffOn_invFun := f.contMDiffOn_invFun.of_le ((by norm_num : 1 ≤ (2 : ℕ∞ω)).trans hn) }
  have hD := differentiableAt_mpullback_in_model I f hn ha hd
  have hdetEq := det_fderiv_mpullback_eq_linearizationAtZero I f hn ha hd hV.zero
  have hDdet : LinearMap.det (fderiv ℝ
      (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I f V) a).toLinearMap ≠ 0 :=
    hdetEq ▸ hdet
  rw [index_eq_localDegree I f₁ ha hV,
    Poincare.LocalDegree.euclideanLocalDegree_eq_sign_det_fderiv _ hD hDdet, hdetEq]

variable [IsManifold I 2 M]

private def twiceDifferentiableIndexChart (x : M) :
    PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
      (EuclideanSpace ℝ (Fin (d + 1))) 2 where
  toPartialEquiv := (indexChart I x).toPartialEquiv
  open_source := (indexChart I x).open_source
  open_target := (indexChart I x).open_target
  contMDiffOn_toFun := by
    simpa only [indexChart, extChartAt_source] using contMDiffOn_extChartAt (I := I) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

theorem index_eq_sign_det_linearizationAtZero
    {V : ∀ x : M, TangentSpace I x} {x : M} (hV : HasContinuousIsolatedZero I V x)
    (hd : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hdet : LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap ≠ 0) :
    index I V x hV =
      (SignType.sign (LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap) : ℤ) := by
  let c := twiceDifferentiableIndexChart I x
  have hx : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv hx
  have hVc : HasContinuousIsolatedZero I V (c.symm (c x)) := hcx.symm ▸ hV
  have hdc : MDifferentiableAt I I.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) (c.symm (c x)) := hcx.symm ▸ hd
  have hLeq : LinearMap.det (linearizationAtZero hdc hVc.zero).toLinearMap =
      LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap := by
    erw [linearizationAtZero_eq_mfderiv hdc hVc.zero,
      linearizationAtZero_eq_mfderiv hd hV.zero]
    erw [hcx]
  have hdetc : LinearMap.det (linearizationAtZero hdc hVc.zero).toLinearMap ≠ 0 := by
    rw [hLeq]
    exact hdet
  simpa only [hLeq, hcx] using
    index_eq_sign_det_linearizationAtZero_in_model I c.symm le_rfl (c.map_source hx) hVc hdc hdetc

theorem hasContinuousIsolatedZero_of_det_linearizationAtZero_ne_zero
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hc : ∃ s ∈ 𝓝 x, ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I M)) s)
    (hd : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hz : V x = 0) (hdet : LinearMap.det (linearizationAtZero hd hz).toLinearMap ≠ 0) :
    HasContinuousIsolatedZero I V x := by
  let c := twiceDifferentiableIndexChart I x
  have hx : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv hx
  have hcc : ∃ s ∈ 𝓝 (c.symm (c x)),
      ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I M)) s := hcx.symm ▸ hc
  have hdc : MDifferentiableAt I I.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) (c.symm (c x)) := hcx.symm ▸ hd
  have hzc : V (c.symm (c x)) = 0 := by
    erw [hcx]
    exact hz
  have hdetc : LinearMap.det (linearizationAtZero hdc hzc).toLinearMap ≠ 0 := by
    erw [linearizationAtZero_eq_mfderiv hdc hzc, hcx]
    exact (linearizationAtZero_eq_mfderiv hd hz) ▸ hdet
  simpa only [hcx] using
    hasContinuousIsolatedZero_of_det_linearizationAtZero_ne_zero_in_model I c.symm le_rfl
      (c.map_source hx) hcc hdc hzc hdetc

theorem hasContinuousIsolatedZero_of_contMDiffAt_det_ne_zero
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hC : ContMDiffAt I I.tangent 1 (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hz : V x = 0)
    (hdet : LinearMap.det (linearizationAtZero (hC.mdifferentiableAt one_ne_zero) hz).toLinearMap ≠ 0) :
    HasContinuousIsolatedZero I V x := by
  obtain ⟨s, hs, hc⟩ := (contMDiffAt_iff_contMDiffOn_nhds
    (show (1 : ℕ∞ω) ≠ ∞ by norm_num)).mp hC
  exact hasContinuousIsolatedZero_of_det_linearizationAtZero_ne_zero I
    ⟨s, hs, hc.continuousOn⟩ (hC.mdifferentiableAt one_ne_zero) hz hdet

theorem exists_index_eq_sign_det_linearizationAtZero
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hC : ContMDiffAt I I.tangent 1 (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hz : V x = 0)
    (hdet : LinearMap.det (linearizationAtZero (hC.mdifferentiableAt one_ne_zero) hz).toLinearMap ≠ 0) :
    ∃ hV : HasContinuousIsolatedZero I V x,
      index I V x hV =
        (SignType.sign (LinearMap.det
          (linearizationAtZero (hC.mdifferentiableAt one_ne_zero) hz).toLinearMap) : ℤ) := by
  let hV := hasContinuousIsolatedZero_of_contMDiffAt_det_ne_zero I hC hz hdet
  exact ⟨hV, index_eq_sign_det_linearizationAtZero I hV
    (hC.mdifferentiableAt one_ne_zero) hdet⟩

end Poincare.VectorField
