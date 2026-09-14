import DifferentialGeometry.Topology.Manifold.OrientedBallChartStraightening
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem pos_of_continuous_ne_zero_of_pos_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hne : ∀ t, f t ≠ 0) (h0 : 0 < f 0) : ∀ t, 0 < f t := by
  intro t
  rcases le_total (0 : ℝ) t with ht | ht
  · by_contra hcon
    have hneg : f t < 0 := lt_of_le_of_ne (not_lt.mp hcon) (hne t)
    have hsub := intermediate_value_Icc' (f := f) ht hf.continuousOn
    have hmem : (0 : ℝ) ∈ Icc (f t) (f 0) := ⟨le_of_lt hneg, le_of_lt h0⟩
    obtain ⟨c, -, hc⟩ := hsub hmem
    exact hne c hc
  · by_contra hcon
    have hneg : f t < 0 := lt_of_le_of_ne (not_lt.mp hcon) (hne t)
    have hsub := intermediate_value_Icc (f := f) ht hf.continuousOn
    have hmem : (0 : ℝ) ∈ Icc (f t) (f 0) := ⟨le_of_lt hneg, le_of_lt h0⟩
    obtain ⟨c, -, hc⟩ := hsub hmem
    exact hne c hc

private theorem orientation_map_coordinates_comp {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [PreconnectedSpace U]
    {o : ManifoldOrientation ThreeModel U 3} (R : Diffeomorph ThreeModel ThreeModel U U ∞)
    (x₀ : U) (T : TangentSpace ThreeModel x₀ ≃ₗ[ℝ] ThreeSpace)
    (T' : TangentSpace ThreeModel (R x₀) ≃ₗ[ℝ] ThreeSpace) (q : Orientation ℝ ThreeSpace (Fin 3))
    (hq : Orientation.map (Fin 3) T (o.orientation x₀) = q) :
    Orientation.map (Fin 3)
        ((T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T') q =
      Orientation.map (Fin 3) T'
        (Orientation.map (Fin 3) (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
          (o.orientation x₀)) := by
  have hsymm : Orientation.map (Fin 3) T.symm (Orientation.map (Fin 3) T (o.orientation x₀)) =
      o.orientation x₀ := by
    rw [← Orientation.map_symm]
    exact Equiv.symm_apply_apply _ _
  rw [← hq]
  calc Orientation.map (Fin 3)
        ((T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T')
        (Orientation.map (Fin 3) T (o.orientation x₀))
      = Orientation.map (Fin 3) T' (Orientation.map (Fin 3)
          (T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv)
          (Orientation.map (Fin 3) T (o.orientation x₀))) :=
        (DifferentialGeometry.VectorBundle.map_orientation_trans_between
          (T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv) T'
          (Orientation.map (Fin 3) T (o.orientation x₀))).symm
    _ = Orientation.map (Fin 3) T'
          (Orientation.map (Fin 3) (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
            (o.orientation x₀)) := by
        congr 1
        rw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between T.symm
          (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
          (Orientation.map (Fin 3) T (o.orientation x₀)), hsymm]

private theorem preservesOrientation_iff_det_pos {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [PreconnectedSpace U]
    {o : ManifoldOrientation ThreeModel U 3} (R : Diffeomorph ThreeModel ThreeModel U U ∞)
    (x₀ : U) (T : TangentSpace ThreeModel x₀ ≃ₗ[ℝ] ThreeSpace)
    (T' : TangentSpace ThreeModel (R x₀) ≃ₗ[ℝ] ThreeSpace) (q : Orientation ℝ ThreeSpace (Fin 3))
    (hq : Orientation.map (Fin 3) T (o.orientation x₀) = q)
    (hq' : Orientation.map (Fin 3) T' (o.orientation (R x₀)) = q) :
    (R.preservesOrientation o o ↔ 0 < LinearMap.det ((T.symm.trans
      (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T').toLinearMap) := by
  constructor
  · intro hpres
    have hkey := (Diffeomorph.preservesOrientation_iff_eq_at R o o x₀).mp hpres
    have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace := by simp
    have hmap : Orientation.map (Fin 3)
        ((T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T')
        q = q := by
      rw [orientation_map_coordinates_comp R x₀ T T' q hq, hkey, hq']
    exact (Orientation.map_eq_iff_det_pos q _ hcard).mp hmap
  · intro hdet
    refine (Diffeomorph.preservesOrientation_iff_eq_at R o o x₀).mpr ?_
    have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace := by simp
    have hmap := (Orientation.map_eq_iff_det_pos q _ hcard).2 hdet
    rw [orientation_map_coordinates_comp R x₀ T T' q hq] at hmap
    exact (Orientation.map (Fin 3) T').injective (hmap.trans hq'.symm)

private theorem eventually_preservesOrientation_iff {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [PreconnectedSpace U]
    {o : ManifoldOrientation ThreeModel U 3} {J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞}
    (hJc : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2))
    (t₀ : ℝ) (x₀ : U) :
    ∀ᶠ t in 𝓝 t₀,
      ((J t).preservesOrientation o o ↔ (J t₀).preservesOrientation o o) := by
  classical
  let R : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞ := fun t => (J t).trans (J t₀).symm
  have hR0 : R t₀ = Diffeomorph.refl ThreeModel U ∞ := by simp [R]
  have hR0val : R t₀ x₀ = x₀ := by rw [hR0]; rfl
  have hRapply : ∀ t : ℝ, ∀ x : U, R t x = (J t₀).symm (J t x) := by
    intro t x
    change ((J t).trans (J t₀).symm) x = (J t₀).symm (J t x)
    rfl
  have hRc : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => R q.1 q.2) := by
    have hfun : (fun q : ℝ × U => R q.1 q.2) =
        fun q : ℝ × U => (J t₀).symm (J q.1 q.2) := by
      funext q
      exact hRapply q.1 q.2
    rw [hfun]
    exact ((J t₀).symm.contMDiff).comp hJc
  have hRcont : ContinuousAt (fun t : ℝ => R t x₀) t₀ :=
    hRc.continuous.continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  have hx₀mem : x₀ ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source ThreeSpace x₀
  obtain ⟨V, hVopen, hxV, hVsub, hVconst⟩ := o.locally_constant x₀ x₀ hx₀mem
  have hVev : ∀ᶠ t in 𝓝 t₀, R t x₀ ∈ V :=
    hRcont.preimage_mem_nhds (hVopen.mem_nhds (by rw [hR0val]; exact hxV))
  have hsrcev : ∀ᶠ t in 𝓝 t₀,
      R t x₀ ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet :=
    hRcont.preimage_mem_nhds
      ((Trivialization.open_baseSet _).mem_nhds (by rw [hR0val]; exact hx₀mem))
  let A : ℝ → ThreeSpace →L[ℝ] ThreeSpace := fun t => inTangentCoordinates ThreeModel ThreeModel
    (fun _ : ℝ => x₀) (fun t : ℝ => R t x₀) (fun t : ℝ => mfderiv ThreeModel ThreeModel (R t) x₀)
    t₀ t
  have hAcont : ContinuousAt A t₀ :=
    (ContMDiffAt.mfderiv (I := ThreeModel) (I' := ThreeModel) (J := 𝓘(ℝ, ℝ))
      (f := fun t : ℝ => (R t : U → U)) (g := fun _ : ℝ => x₀) (x₀ := t₀) (n := ∞) (m := 0)
      hRc.contMDiffAt contMDiffAt_const (by simp)).continuousAt
  have hAeq (t : ℝ)
      (hsrc : R t x₀ ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) :
      (((DifferentialGeometry.tangentChartEquiv ThreeModel U x₀ x₀ hx₀mem).symm.trans
        ((R t).mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans
        (DifferentialGeometry.tangentChartEquiv ThreeModel U x₀ (R t x₀) hsrc)).toLinearMap
      = (A t : ThreeSpace →ₗ[ℝ] ThreeSpace) := by
    have h := ContinuousLinearMap.inCoordinates_eq (F := ThreeSpace) (E := TangentSpace ThreeModel)
      (F' := ThreeSpace) (E' := TangentSpace ThreeModel) (x₀ := x₀) (x := x₀)
      (y₀ := x₀) (y := R t x₀) (ϕ := mfderiv ThreeModel ThreeModel (R t) x₀) hx₀mem hsrc
    have hA : A t = ContinuousLinearMap.inCoordinates ThreeSpace (TangentSpace ThreeModel)
        ThreeSpace (TangentSpace ThreeModel) x₀ x₀ x₀ (R t x₀)
        (mfderiv ThreeModel ThreeModel (R t) x₀) := by
      change inTangentCoordinates ThreeModel ThreeModel (fun _ : ℝ => x₀) (fun t : ℝ => R t x₀)
        (fun t : ℝ => mfderiv ThreeModel ThreeModel (R t) x₀) t₀ t = _
      simp only [inTangentCoordinates]
      rw [hR0val]
    apply LinearMap.ext
    intro v
    rw [hA, h]
    rfl
  have key (t : ℝ)
      (hsrc : R t x₀ ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet)
      (hVt : R t x₀ ∈ V) :
      ((R t).preservesOrientation o o ↔ 0 < LinearMap.det
        ((((DifferentialGeometry.tangentChartEquiv ThreeModel U x₀ x₀ hx₀mem).symm.trans
          ((R t).mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans
          (DifferentialGeometry.tangentChartEquiv ThreeModel U x₀ (R t x₀) hsrc)).toLinearMap)) :=
    preservesOrientation_iff_det_pos (R t) x₀ _ _ _ rfl (hVconst (R t x₀) hVt)
  have hdetcont : ContinuousAt (fun t : ℝ => LinearMap.det
      ((A t : ThreeSpace →L[ℝ] ThreeSpace) : ThreeSpace →ₗ[ℝ] ThreeSpace)) t₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hAcont
  have hsrc₀ : R t₀ x₀ ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet := by
    rw [hR0val]
    exact hx₀mem
  have hpres₀ : (R t₀).preservesOrientation o o := by
    rw [hR0]
    exact Diffeomorph.preservesOrientation_refl o
  have hdetpos₀ : 0 < LinearMap.det ((A t₀ : ThreeSpace →L[ℝ] ThreeSpace) :
      ThreeSpace →ₗ[ℝ] ThreeSpace) := by
    have h := (key t₀ hsrc₀ hVev.self_of_nhds).mp hpres₀
    rwa [hAeq t₀ hsrc₀] at h
  have hpdev : ∀ᶠ t in 𝓝 t₀, 0 < LinearMap.det
      ((A t : ThreeSpace →L[ℝ] ThreeSpace) : ThreeSpace →ₗ[ℝ] ThreeSpace) :=
    hdetcont.eventually (isOpen_Ioi.mem_nhds hdetpos₀)
  have hRpres : ∀ᶠ t in 𝓝 t₀, (R t).preservesOrientation o o := by
    filter_upwards [hpdev, hsrcev, hVev] with t hpos hsrc hVt
    have hpos' : 0 < LinearMap.det
        ((((DifferentialGeometry.tangentChartEquiv ThreeModel U x₀ x₀ hx₀mem).symm.trans
          ((R t).mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans
          (DifferentialGeometry.tangentChartEquiv ThreeModel U x₀ (R t x₀) hsrc)).toLinearMap) := by
      rw [← hAeq t hsrc] at hpos
      exact hpos
    exact (key t hsrc hVt).mpr hpos'
  have hRt (t : ℝ) : (R t).trans (J t₀) = J t := by
    ext x
    change J t₀ (R t x) = J t x
    rw [hRapply t x, Diffeomorph.apply_symm_apply]
  have hsymm_symm (Φ : Diffeomorph ThreeModel ThreeModel U U ∞) : Φ.symm.symm = Φ :=
    Diffeomorph.toEquiv_inj.mp (by simp [Diffeomorph.symm_toEquiv])
  have hRtsym (t : ℝ) : (R t).symm.trans (J t) = J t₀ := by
    ext x
    change J t ((R t).symm x) = J t₀ x
    have hsym : (R t).symm x = (J t).symm (J t₀ x) := by
      change ((J t).trans (J t₀).symm).symm x = _
      rw [Diffeomorph.symm_trans']
      simp [hsymm_symm]
    rw [hsym, Diffeomorph.apply_symm_apply]
  filter_upwards [hRpres] with t hR
  refine ⟨fun ht => ?_, fun ht₀ => ?_⟩
  · rw [← hRtsym t]
    exact Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm hR) ht
  · rw [← hRt t]
    exact Diffeomorph.preservesOrientation_trans hR ht₀

theorem preservesOrientation_of_jointlySmooth_isotopy {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [PreconnectedSpace U]
    (o : ManifoldOrientation ThreeModel U 3) (J : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ0 : J 0 = Diffeomorph.refl ThreeModel U ∞)
    (hJc : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2)) :
    ∀ t, (J t).preservesOrientation o o := by
  classical
  rcases isEmpty_or_nonempty U with hU | hU
  · intro t x
    exact isEmptyElim x
  · obtain ⟨x₀⟩ := hU
    intro t₁
    let f : ℝ → ℝ := fun t => if (J t).preservesOrientation o o then 1 else -1
    have hloc : ∀ t, ∀ᶠ s in 𝓝 t, f s = f t := by
      intro t
      have h := eventually_preservesOrientation_iff (o := o) hJc t x₀
      filter_upwards [h] with s hs
      simp only [f]
      rw [hs]
    have hfcont : Continuous f := by
      rw [continuous_iff_continuousAt]
      intro t
      refine (continuousAt_const : ContinuousAt (fun _ : ℝ => f t) t).congr ?_
      filter_upwards [hloc t] with s hs
      exact hs.symm
    have hfne : ∀ t, f t ≠ 0 := by
      intro t
      simp only [f]
      split <;> norm_num
    have hf0 : 0 < f 0 := by
      simp only [f]
      rw [hJ0]
      simp [Diffeomorph.preservesOrientation_refl]
    have hpos := pos_of_continuous_ne_zero_of_pos_zero hfcont hfne hf0 t₁
    by_contra hcon
    simp only [f, hcon, if_false] at hpos
    norm_num at hpos

theorem isotopyPreservesOrientation_holds : isotopyPreservesOrientation.{u} := by
  intro U _ _ _ _ _ o J hJ0 hJc _
  exact preservesOrientation_of_jointlySmooth_isotopy o J hJ0 hJc 1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
