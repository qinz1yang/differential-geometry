import DifferentialGeometry.Topology.Manifold.IsotopyOrientation

/-!
# Jointly smooth isotopies preserve orientation (any model with corners)

`IsotopyOrientation.lean` proves that every member of a jointly smooth isotopy starting at the
identity preserves a given orientation, for the boundaryless three-dimensional model only. The
argument is chart-local and works verbatim for an arbitrary model with corners `I` on a
finite-dimensional space (in particular for manifolds with boundary, model `𝓡∂ n`): near each time
`t₀`, the sign of the determinant of `d (J t ∘ (J t₀)⁻¹)` at a base point, read in one tangent chart,
is continuous in `t`, hence the property "preserves the orientation" is locally constant in `t`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {U : Type*} [TopologicalSpace U] [ChartedSpace H U] [IsManifold I ∞ U] {n : ℕ}

private theorem orientation_map_coordinates_comp_model {o : ManifoldOrientation I U n}
    (R : U ≃ₘ⟮I, I⟯ U) (x₀ : U) (T : TangentSpace I x₀ ≃ₗ[ℝ] E)
    (T' : TangentSpace I (R x₀) ≃ₗ[ℝ] E) (q : Orientation ℝ E (Fin n))
    (hq : Orientation.map (Fin n) T (o.orientation x₀) = q) :
    Orientation.map (Fin n)
        ((T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T') q =
      Orientation.map (Fin n) T'
        (Orientation.map (Fin n) (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
          (o.orientation x₀)) := by
  have hsymm : Orientation.map (Fin n) T.symm (Orientation.map (Fin n) T (o.orientation x₀)) =
      o.orientation x₀ := by
    rw [← Orientation.map_symm]
    exact Equiv.symm_apply_apply _ _
  rw [← hq]
  calc Orientation.map (Fin n)
        ((T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T')
        (Orientation.map (Fin n) T (o.orientation x₀))
      = Orientation.map (Fin n) T' (Orientation.map (Fin n)
          (T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv)
          (Orientation.map (Fin n) T (o.orientation x₀))) :=
        (DifferentialGeometry.VectorBundle.map_orientation_trans_between
          (T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv) T'
          (Orientation.map (Fin n) T (o.orientation x₀))).symm
    _ = Orientation.map (Fin n) T'
          (Orientation.map (Fin n) (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
            (o.orientation x₀)) := by
        congr 1
        rw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between T.symm
          (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
          (Orientation.map (Fin n) T (o.orientation x₀)), hsymm]

private theorem preservesOrientation_iff_det_pos_model [PreconnectedSpace U]
    {o : ManifoldOrientation I U n} {R : U ≃ₘ⟮I, I⟯ U}
    (x₀ : U) (T : TangentSpace I x₀ ≃ₗ[ℝ] E)
    (T' : TangentSpace I (R x₀) ≃ₗ[ℝ] E) (q : Orientation ℝ E (Fin n))
    (hq : Orientation.map (Fin n) T (o.orientation x₀) = q)
    (hq' : Orientation.map (Fin n) T' (o.orientation (R x₀)) = q) :
    (R.preservesOrientation o o ↔ 0 < LinearMap.det ((T.symm.trans
      (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T').toLinearMap) := by
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E := by
    rw [Fintype.card_fin, o.dimension_eq]
  constructor
  · intro hpres
    have hkey := (Diffeomorph.preservesOrientation_iff_eq_at R o o x₀).mp hpres
    have hmap : Orientation.map (Fin n)
        ((T.symm.trans (R.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans T')
        q = q := by
      rw [orientation_map_coordinates_comp_model R x₀ T T' q hq, hkey, hq']
    exact (Orientation.map_eq_iff_det_pos q _ hcard).mp hmap
  · intro hdet
    refine (Diffeomorph.preservesOrientation_iff_eq_at R o o x₀).mpr ?_
    have hmap := (Orientation.map_eq_iff_det_pos q _ hcard).2 hdet
    rw [orientation_map_coordinates_comp_model R x₀ T T' q hq] at hmap
    exact (Orientation.map (Fin n) T').injective (hmap.trans hq'.symm)

/-- Along a jointly smooth isotopy, "preserves the orientation" is locally constant in time. -/
theorem eventually_preservesOrientation_iff_of_contMDiff_isotopy [PreconnectedSpace U]
    {o : ManifoldOrientation I U n} {J : ℝ → (U ≃ₘ⟮I, I⟯ U)}
    (hJc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => J q.1 q.2))
    (t₀ : ℝ) (x₀ : U) :
    ∀ᶠ t in 𝓝 t₀,
      ((J t).preservesOrientation o o ↔ (J t₀).preservesOrientation o o) := by
  classical
  let R : ℝ → (U ≃ₘ⟮I, I⟯ U) := fun t => (J t).trans (J t₀).symm
  have hR0 : R t₀ = Diffeomorph.refl I U ∞ := by simp [R]
  have hR0val : R t₀ x₀ = x₀ := by rw [hR0]; rfl
  have hRapply : ∀ t : ℝ, ∀ x : U, R t x = (J t₀).symm (J t x) := by
    intro t x
    change ((J t).trans (J t₀).symm) x = (J t₀).symm (J t x)
    rfl
  have hRc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => R q.1 q.2) := by
    have hfun : (fun q : ℝ × U => R q.1 q.2) =
        fun q : ℝ × U => (J t₀).symm (J q.1 q.2) := by
      funext q
      exact hRapply q.1 q.2
    rw [hfun]
    exact ((J t₀).symm.contMDiff).comp hJc
  have hRcont : ContinuousAt (fun t : ℝ => R t x₀) t₀ :=
    hRc.continuous.continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  have hx₀mem : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H x₀
  obtain ⟨V, hVopen, hxV, hVsub, hVconst⟩ := o.locally_constant x₀ x₀ hx₀mem
  have hVev : ∀ᶠ t in 𝓝 t₀, R t x₀ ∈ V :=
    hRcont.preimage_mem_nhds (hVopen.mem_nhds (by rw [hR0val]; exact hxV))
  have hsrcev : ∀ᶠ t in 𝓝 t₀,
      R t x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    hRcont.preimage_mem_nhds
      ((Trivialization.open_baseSet _).mem_nhds (by rw [hR0val]; exact hx₀mem))
  let A : ℝ → E →L[ℝ] E := fun t => inTangentCoordinates I I
    (fun _ : ℝ => x₀) (fun t : ℝ => R t x₀) (fun t : ℝ => mfderiv I I (R t) x₀) t₀ t
  have hAcont : ContinuousAt A t₀ :=
    (ContMDiffAt.mfderiv (I := I) (I' := I) (J := 𝓘(ℝ, ℝ))
      (f := fun t : ℝ => (R t : U → U)) (g := fun _ : ℝ => x₀) (x₀ := t₀) (n := ∞) (m := 0)
      hRc.contMDiffAt contMDiffAt_const (by simp)).continuousAt
  have hAeq (t : ℝ)
      (hsrc : R t x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
      (((DifferentialGeometry.tangentChartEquiv I U x₀ x₀ hx₀mem).symm.trans
        ((R t).mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans
        (DifferentialGeometry.tangentChartEquiv I U x₀ (R t x₀) hsrc)).toLinearMap
      = (A t : E →ₗ[ℝ] E) := by
    have h := ContinuousLinearMap.inCoordinates_eq (F := E) (E := TangentSpace I)
      (F' := E) (E' := TangentSpace I) (x₀ := x₀) (x := x₀)
      (y₀ := x₀) (y := R t x₀) (ϕ := mfderiv I I (R t) x₀) hx₀mem hsrc
    have hA : A t = ContinuousLinearMap.inCoordinates E (TangentSpace I)
        E (TangentSpace I) x₀ x₀ x₀ (R t x₀)
        (mfderiv I I (R t) x₀) := by
      change inTangentCoordinates I I (fun _ : ℝ => x₀) (fun t : ℝ => R t x₀)
        (fun t : ℝ => mfderiv I I (R t) x₀) t₀ t = _
      simp only [inTangentCoordinates]
      rw [hR0val]
    apply LinearMap.ext
    intro v
    rw [hA, h]
    rfl
  have key (t : ℝ)
      (hsrc : R t x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (hVt : R t x₀ ∈ V) :
      ((R t).preservesOrientation o o ↔ 0 < LinearMap.det
        ((((DifferentialGeometry.tangentChartEquiv I U x₀ x₀ hx₀mem).symm.trans
          ((R t).mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans
          (DifferentialGeometry.tangentChartEquiv I U x₀ (R t x₀) hsrc)).toLinearMap)) :=
    preservesOrientation_iff_det_pos_model (R := R t) x₀ _ _ _ rfl (hVconst (R t x₀) hVt)
  have hdetcont : ContinuousAt (fun t : ℝ => LinearMap.det
      ((A t : E →L[ℝ] E) : E →ₗ[ℝ] E)) t₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hAcont
  have hsrc₀ : R t₀ x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [hR0val]
    exact hx₀mem
  have hpres₀ : (R t₀).preservesOrientation o o := by
    rw [hR0]
    exact Diffeomorph.preservesOrientation_refl o
  have hdetpos₀ : 0 < LinearMap.det ((A t₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    have h := (key t₀ hsrc₀ hVev.self_of_nhds).mp hpres₀
    rwa [hAeq t₀ hsrc₀] at h
  have hpdev : ∀ᶠ t in 𝓝 t₀, 0 < LinearMap.det ((A t : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
    hdetcont.eventually (isOpen_Ioi.mem_nhds hdetpos₀)
  have hRpres : ∀ᶠ t in 𝓝 t₀, (R t).preservesOrientation o o := by
    filter_upwards [hpdev, hsrcev, hVev] with t hpos hsrc hVt
    have hpos' : 0 < LinearMap.det
        ((((DifferentialGeometry.tangentChartEquiv I U x₀ x₀ hx₀mem).symm.trans
          ((R t).mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv).trans
          (DifferentialGeometry.tangentChartEquiv I U x₀ (R t x₀) hsrc)).toLinearMap) := by
      rw [← hAeq t hsrc] at hpos
      exact hpos
    exact (key t hsrc hVt).mpr hpos'
  have hRt (t : ℝ) : (R t).trans (J t₀) = J t := by
    ext x
    change J t₀ (R t x) = J t x
    rw [hRapply t x, Diffeomorph.apply_symm_apply]
  have hsymm_symm (Ψ : U ≃ₘ⟮I, I⟯ U) : Ψ.symm.symm = Ψ :=
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

/-- Every member of a jointly smooth isotopy of diffeomorphisms starting at the identity preserves
a given orientation of a connected manifold (any model with corners, e.g. `𝓡∂ n`). -/
theorem preservesOrientation_of_contMDiff_isotopy [PreconnectedSpace U]
    (o : ManifoldOrientation I U n) (J : ℝ → (U ≃ₘ⟮I, I⟯ U))
    (hJ0 : J 0 = Diffeomorph.refl I U ∞)
    (hJc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => J q.1 q.2)) (t : ℝ) :
    (J t).preservesOrientation o o := by
  classical
  rcases isEmpty_or_nonempty U with hU | hU
  · intro x
    exact isEmptyElim x
  · obtain ⟨x₀⟩ := hU
    let f : ℝ → ℝ := fun t => if (J t).preservesOrientation o o then 1 else -1
    have hloc : ∀ t, ∀ᶠ s in 𝓝 t, f s = f t := by
      intro t
      have h := eventually_preservesOrientation_iff_of_contMDiff_isotopy (o := o) hJc t x₀
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
    have hpos :=
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pos_of_continuous_ne_zero_of_pos_zero
        hfcont hfne hf0 t
    by_contra hcon
    simp only [f, hcon, ite_false] at hpos
    norm_num at hpos

/-- Flow form: the time-`t` map of a jointly smooth flow (`Φ 0 = id` pointwise) preserves a given
orientation of a connected manifold. -/
theorem preservesOrientation_of_contMDiff_flow [PreconnectedSpace U]
    (o : ManifoldOrientation I U n) (Φ : ℝ → (U ≃ₘ⟮I, I⟯ U))
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦc : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => Φ q.1 q.2)) (t : ℝ) :
    (Φ t).preservesOrientation o o :=
  preservesOrientation_of_contMDiff_isotopy o Φ (by ext x; exact hΦ0 x) hΦc t

end DifferentialGeometry.Topology.Manifold
