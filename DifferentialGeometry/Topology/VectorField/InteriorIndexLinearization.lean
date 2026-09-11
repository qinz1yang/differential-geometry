import DifferentialGeometry.Topology.VectorField.InteriorIndex
import DifferentialGeometry.Topology.VectorField.IndexLinearization

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField

variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]

theorem interiorIndex_eq_sign_det_linearizationAtZero_in_model {n : ℕ∞ω}
    (f : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
      (EuclideanSpace ℝ (Fin (d + 1))) M n) (hn : 2 ≤ n)
    {V : ∀ x : M, TangentSpace I x} {a : EuclideanSpace ℝ (Fin (d + 1))}
    (ha : a ∈ f.source) (hV : HasContinuousIsolatedZero I V (f a))
    (hd : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) (f a))
    (hdet : LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap ≠ 0) :
    interiorIndex I V (f a) hV
        (DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph I n f
          (ne_of_gt (lt_of_lt_of_le (by norm_num) hn)) ha) =
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
  rw [interiorIndex_eq_localDegree I f₁ ha hV,
    DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sign_det_fderiv _ hD hDdet, hdetEq]

variable [IsManifold I 2 M]

theorem interiorIndex_eq_sign_det_linearizationAtZero
    {V : ∀ x : M, TangentSpace I x} {x : M} (hx : I.IsInteriorPoint x)
    (hV : HasContinuousIsolatedZero I V x)
    (hd : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hdet : LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap ≠ 0) :
    interiorIndex I V x hV hx =
      (SignType.sign (LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap) : ℤ) := by
  let c := DifferentialGeometry.Manifold.interiorChart I 2 x
  have hxc : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 2 x).mpr hx
  have hcx : c.symm (c x) = x := c.left_inv hxc
  have hVc : HasContinuousIsolatedZero I V (c.symm (c x)) := hcx.symm ▸ hV
  have hdc : MDifferentiableAt I I.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) (c.symm (c x)) := hcx.symm ▸ hd
  have hLeq : LinearMap.det (linearizationAtZero hdc hVc.zero).toLinearMap =
      LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap := by
    erw [linearizationAtZero_eq_mfderiv hdc hVc.zero,
      linearizationAtZero_eq_mfderiv hd hV.zero, hcx]
  have hdetc : LinearMap.det (linearizationAtZero hdc hVc.zero).toLinearMap ≠ 0 := by
    rw [hLeq]
    exact hdet
  simpa only [hLeq, hcx] using
    interiorIndex_eq_sign_det_linearizationAtZero_in_model I c.symm le_rfl
      (c.map_source hxc) hVc hdc hdetc

theorem hasContinuousIsolatedZero_of_isInteriorPoint_det_ne_zero
    {V : ∀ x : M, TangentSpace I x} {x : M} (hx : I.IsInteriorPoint x)
    (hc : ∃ s ∈ 𝓝 x, ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I M)) s)
    (hd : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hz : V x = 0) (hdet : LinearMap.det (linearizationAtZero hd hz).toLinearMap ≠ 0) :
    HasContinuousIsolatedZero I V x := by
  let c := DifferentialGeometry.Manifold.interiorChart I 2 x
  have hxc : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I 2 x).mpr hx
  have hcx : c.symm (c x) = x := c.left_inv hxc
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
      (c.map_source hxc) hcc hdc hzc hdetc

theorem hasContinuousIsolatedZero_of_isInteriorPoint_contMDiffAt_det_ne_zero
    {V : ∀ x : M, TangentSpace I x} {x : M} (hx : I.IsInteriorPoint x)
    (hC : ContMDiffAt I I.tangent 1 (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hz : V x = 0)
    (hdet : LinearMap.det (linearizationAtZero (hC.mdifferentiableAt one_ne_zero) hz).toLinearMap ≠ 0) :
    HasContinuousIsolatedZero I V x := by
  obtain ⟨s, hs, hc⟩ := (contMDiffAt_iff_contMDiffOn_nhds
    (show (1 : ℕ∞ω) ≠ ∞ by norm_num)).mp hC
  exact hasContinuousIsolatedZero_of_isInteriorPoint_det_ne_zero I hx
    ⟨s, hs, hc.continuousOn⟩ (hC.mdifferentiableAt one_ne_zero) hz hdet

theorem exists_interiorIndex_eq_sign_det_linearizationAtZero
    {V : ∀ x : M, TangentSpace I x} {x : M} (hx : I.IsInteriorPoint x)
    (hC : ContMDiffAt I I.tangent 1 (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hz : V x = 0)
    (hdet : LinearMap.det (linearizationAtZero (hC.mdifferentiableAt one_ne_zero) hz).toLinearMap ≠ 0) :
    ∃ hV : HasContinuousIsolatedZero I V x,
      interiorIndex I V x hV hx =
        (SignType.sign (LinearMap.det
          (linearizationAtZero (hC.mdifferentiableAt one_ne_zero) hz).toLinearMap) : ℤ) := by
  let hV := hasContinuousIsolatedZero_of_isInteriorPoint_contMDiffAt_det_ne_zero I hx hC hz hdet
  exact ⟨hV, interiorIndex_eq_sign_det_linearizationAtZero I hx hV
    (hC.mdifferentiableAt one_ne_zero) hdet⟩

end DifferentialGeometry.VectorField
