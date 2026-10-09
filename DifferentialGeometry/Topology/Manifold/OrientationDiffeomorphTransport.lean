import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [FiniteDimensional ℝ E] in
theorem continuousAt_mfderiv_coordinates (f : M ≃ₘ⟮I, I⟯ N) (x₀ : M) :
    ContinuousAt (fun x : M =>
      (trivializationAt E (TangentSpace I) (f x₀)).continuousLinearMapAt ℝ (f x) ∘L
        mfderiv% f x ∘L
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ x) x₀ := by
  have hmain : ContinuousAt (inTangentCoordinates I I id f (mfderiv% f) x₀) x₀ :=
    (ContMDiffAt.mfderiv_const (I := I) (I' := I) (f := f) (x₀ := x₀) (n := ∞) (m := 0)
      f.contMDiff.contMDiffAt (by simp)).continuousAt
  refine hmain.congr ?_
  filter_upwards [((chartAt H x₀).open_source).mem_nhds (mem_chart_source H x₀),
    f.continuous.continuousAt.preimage_mem_nhds
      (((chartAt H (f x₀)).open_source).mem_nhds (mem_chart_source H (f x₀)))]
    with x hx hfx
  rw [inTangentCoordinates_eq (I := I) (I' := I) (f := id) (g := (f : M → N))
      (ϕ := fun x => mfderiv% f x) (x₀ := x₀) (x := x) hx hfx]
  simp only [id_eq]
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := N)
      (b₀ := f x₀) (b := f x) hfx,
    ← TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := x₀) (b := x) hx]
  rfl

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem isCompatibleOrientation_diffeomorph_map
    (f : M ≃ₘ⟮I, I⟯ N) (hdim : Module.finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I) o) :
    DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I)
      (fun y : N => Orientation.map (Fin n)
        ((f.mfderivToContinuousLinearEquiv (by simp) (f.symm y)).toLinearEquiv) (o (f.symm y))) := by
  classical
  let mfd : ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I (f x) :=
    fun x => f.mfderivToContinuousLinearEquiv (by simp) x
  change DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I)
    (fun y : N => Orientation.map (Fin n) ((mfd (f.symm y)).toLinearEquiv) (o (f.symm y)))
  have hmfd : ∀ x : M, mfd x = mfderiv% f x := fun x => rfl
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_compatibleOrientation I hdim o ho
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E := by simpa using hdim.symm
  intro y₀
  let x₀ : M := f.symm y₀
  have hfx₀ : f x₀ = y₀ := f.apply_symm_apply y₀
  have hM₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x₀
  have hN₀ : y₀ ∈ (trivializationAt E (TangentSpace I) (f x₀)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, ← hfx₀]; exact mem_chart_source H (f x₀)
  obtain ⟨U, hUopen, hx₀U, hUsub, hconst⟩ := O.locally_constant x₀ x₀ hM₀
  let q : Orientation ℝ E (Fin n) := Orientation.map (Fin n)
    (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x₀ hM₀).toLinearEquiv)
    (o x₀)
  have hq : ∀ y (hy : y ∈ U), Orientation.map (Fin n)
      (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ y (hUsub hy)).toLinearEquiv)
      (o y) = q := by
    intro y hy
    have h1 := hconst y hy
    have hE : tangentChartEquiv I M x₀ y (hUsub hy) =
        (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ y (hUsub hy)).toLinearEquiv) :=
      LinearEquiv.ext fun v => rfl
    have hE₀ : tangentChartEquiv I M x₀ x₀ hM₀ =
        (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x₀ hM₀).toLinearEquiv) :=
      LinearEquiv.ext fun v => rfl
    rw [hE, hE₀, hO] at h1
    exact h1
  let L : M → E →L[ℝ] E := fun x =>
      (trivializationAt E (TangentSpace I) (f x₀)).continuousLinearMapAt ℝ (f x) ∘L
        mfderiv% f x ∘L (trivializationAt E (TangentSpace I) x₀).symmL ℝ x
  have hLcont : ContinuousAt L x₀ := continuousAt_mfderiv_coordinates f x₀
  have hdetcont : ContinuousAt
      (fun y : N => LinearMap.det ((L (f.symm y) : E →L[ℝ] E) : E →ₗ[ℝ] E)) y₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (hLcont.comp (f.symm.continuous.continuousAt))
  let Cfun : N → E ≃ₗ[ℝ] E := fun y =>
    if hb : y ∈ (trivializationAt E (TangentSpace I) (f x₀)).baseSet then
      if hm : f.symm y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet then
        ((((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ (f.symm y) hm).symm.trans
          ((mfd (f.symm y)).trans
            ((trivializationAt E (TangentSpace I) (f x₀)).continuousLinearEquivAt ℝ y hb))).toLinearEquiv)
      else LinearEquiv.refl ℝ E
    else LinearEquiv.refl ℝ E
  have hCfun_apply (y : N)
      (hb : y ∈ (trivializationAt E (TangentSpace I) (f x₀)).baseSet)
      (hm : f.symm y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
      Cfun y =
        ((((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ (f.symm y) hm).symm.trans
          ((mfd (f.symm y)).trans
            ((trivializationAt E (TangentSpace I) (f x₀)).continuousLinearEquivAt ℝ y hb))).toLinearEquiv) := by
    simp only [Cfun]
    rw [dite_eq_left hb, dite_eq_left hm]
  have hCLM : ∀ (y : N) (hb : y ∈ (trivializationAt E (TangentSpace I) (f x₀)).baseSet)
      (hm : f.symm y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet),
      (Cfun y : E →ₗ[ℝ] E) = ((L (f.symm y) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    intro y hb hm
    rw [hCfun_apply y hb hm]
    ext v
    simp only [L, ContinuousLinearEquiv.trans_toLinearEquiv,
      ContinuousLinearEquiv.toLinearEquiv_symm]
    change (↑(Trivialization.continuousLinearEquivAt ℝ
          (trivializationAt E (TangentSpace I) (f x₀)) y hb) : TangentSpace I y →L[ℝ] E)
        ((↑(mfd (f.symm y)) :
            TangentSpace I (f.symm y) →L[ℝ] TangentSpace I (f (f.symm y)))
          ((↑((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ
              (f.symm y) hm).symm : E →L[ℝ] TangentSpace I (f.symm y)) v))
      = ((trivializationAt E (TangentSpace I) (f x₀)).continuousLinearMapAt ℝ (f (f.symm y)))
          ((mfderiv% f (f.symm y))
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (f.symm y) v))
    rw [Trivialization.coe_continuousLinearEquivAt_eq' (R := ℝ)
        (trivializationAt E (TangentSpace I) (f x₀)) hb]
    rw [Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ)
        (trivializationAt E (TangentSpace I) x₀) hm]
    rw [hmfd (f.symm y)]
    rw [Diffeomorph.apply_symm_apply]
    rw [Diffeomorph.apply_symm_apply]
  have hev : (fun y : N => LinearMap.det ((Cfun y : E →ₗ[ℝ] E))) =ᶠ[𝓝 y₀]
      (fun y : N => LinearMap.det ((L (f.symm y) : E →L[ℝ] E) : E →ₗ[ℝ] E)) := by
    filter_upwards [((trivializationAt E (TangentSpace I) (f x₀)).open_baseSet).mem_nhds hN₀,
      f.symm.continuous.continuousAt.preimage_mem_nhds
        (((trivializationAt E (TangentSpace I) x₀).open_baseSet).mem_nhds hM₀)]
      with y hyb hym
    rw [hCLM y hyb hym]
  have hdetC : ContinuousAt (fun y : N => LinearMap.det ((Cfun y : E →ₗ[ℝ] E))) y₀ :=
    hdetcont.congr hev.symm
  have hdet₀ : LinearMap.det ((Cfun y₀ : E →ₗ[ℝ] E)) ≠ 0 := (Cfun y₀).isUnit_det'.ne_zero
  have key : ∀ (y : N) (hb : y ∈ (trivializationAt E (TangentSpace I) (f x₀)).baseSet)
      (hu : f.symm y ∈ U),
      Orientation.map (Fin n)
        (((trivializationAt E (TangentSpace I) (f x₀)).continuousLinearEquivAt ℝ y hb).toLinearEquiv)
        (Orientation.map (Fin n) ((mfd (f.symm y)).toLinearEquiv) (o (f.symm y)))
      = Orientation.map (Fin n) (Cfun y) q := by
    intro y hb hu
    have hoq : o (f.symm y) = Orientation.map (Fin n)
        (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ (f.symm y) (hUsub hu)).toLinearEquiv.symm) q := by
      have h1 := hq (f.symm y) hu
      rw [← h1, ← Orientation.map_symm, Equiv.symm_apply_apply]
    rw [hoq]
    let A : E ≃ₗ[ℝ] E :=
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ (f.symm y)
        (hUsub hu)).toLinearEquiv.symm
    let B : E ≃ₗ[ℝ] E := (mfd (f.symm y)).toLinearEquiv
    let D : E ≃ₗ[ℝ] E :=
      ((trivializationAt E (TangentSpace I) (f x₀)).continuousLinearEquivAt ℝ y hb).toLinearEquiv
    change Orientation.map (Fin n) D (Orientation.map (Fin n) B (Orientation.map (Fin n) A q)) =
      Orientation.map (Fin n) (Cfun y) q
    calc Orientation.map (Fin n) D (Orientation.map (Fin n) B (Orientation.map (Fin n) A q))
        = Orientation.map (Fin n) (B.trans D) (Orientation.map (Fin n) A q) :=
          DifferentialGeometry.VectorBundle.map_orientation_trans_between B D _
      _ = Orientation.map (Fin n) (A.trans (B.trans D)) q :=
          DifferentialGeometry.VectorBundle.map_orientation_trans_between A (B.trans D) q
      _ = Orientation.map (Fin n) (Cfun y) q := by
          rw [hCfun_apply y hb (hUsub hu)]
          simp only [ContinuousLinearEquiv.trans_toLinearEquiv,
            ContinuousLinearEquiv.toLinearEquiv_symm, A, B, D]
  rcases lt_or_gt_of_ne hdet₀ with hneg | hpos
  · refine ⟨trivializationAt E (TangentSpace I) (f x₀), inferInstance,
      (trivializationAt E (TangentSpace I) (f x₀)).baseSet ∩ f.symm ⁻¹' U ∩
        {y : N | LinearMap.det ((Cfun y : E →ₗ[ℝ] E)) < 0}, ?_, (fun y hy => hy.1.1), -q, ?_⟩
    · exact Filter.inter_mem (Filter.inter_mem
        (((trivializationAt E (TangentSpace I) (f x₀)).open_baseSet).mem_nhds hN₀)
        (f.symm.continuous.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hx₀U)))
        (hdetC.eventually (isOpen_Iio.mem_nhds hneg))
    · intro y hy
      obtain ⟨⟨hyb, hyU⟩, hsign⟩ := hy
      rw [key y hyb hyU, (Orientation.map_eq_neg_iff_det_neg q (Cfun y) hcard).2 hsign]
  · refine ⟨trivializationAt E (TangentSpace I) (f x₀), inferInstance,
      (trivializationAt E (TangentSpace I) (f x₀)).baseSet ∩ f.symm ⁻¹' U ∩
        {y : N | 0 < LinearMap.det ((Cfun y : E →ₗ[ℝ] E))}, ?_, (fun y hy => hy.1.1), q, ?_⟩
    · exact Filter.inter_mem (Filter.inter_mem
        (((trivializationAt E (TangentSpace I) (f x₀)).open_baseSet).mem_nhds hN₀)
        (f.symm.continuous.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hx₀U)))
        (hdetC.eventually (isOpen_Ioi.mem_nhds hpos))
    · intro y hy
      obtain ⟨⟨hyb, hyU⟩, hsign⟩ := hy
      rw [key y hyb hyU, (Orientation.map_eq_iff_det_pos q (Cfun y) hcard).2 hsign]

set_option backward.isDefEq.respectTransparency false in
theorem exists_manifoldOrientation_diffeomorph_map (f : M ≃ₘ⟮I, I⟯ N)
    (O : ManifoldOrientation I M n) :
    ∃ O' : ManifoldOrientation I N n,
      O'.orientation = fun y : N => Orientation.map (Fin n)
        ((f.mfderivToContinuousLinearEquiv (by simp) (f.symm y)).toLinearEquiv)
        (O.orientation (f.symm y)) :=
  exists_manifoldOrientation_eq_of_compatibleOrientation I O.dimension_eq _
    (isCompatibleOrientation_diffeomorph_map f O.dimension_eq O.orientation
      (isCompatibleOrientation_of_manifoldOrientation O))

end DifferentialGeometry.Topology.Manifold

namespace Diffeomorph

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem preservesOrientation_of_eq_at [PreconnectedSpace N]
    (f : M ≃ₘ⟮I, I⟯ N) (oM : DifferentialGeometry.ManifoldOrientation I M n)
    (oN : DifferentialGeometry.ManifoldOrientation I N n) (x₀ : M)
    (h₀ : Orientation.map (Fin n)
        ((f.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv)
        (oM.orientation x₀) = oN.orientation (f x₀)) :
    f.preservesOrientation oM oN := by
  classical
  let mfd : ∀ x : M, TangentSpace I x ≃L[ℝ] TangentSpace I (f x) :=
    fun x => f.mfderivToContinuousLinearEquiv (by simp) x
  have h₀' : Orientation.map (Fin n) ((mfd x₀).toLinearEquiv) (oM.orientation x₀) =
      oN.orientation (f x₀) := h₀
  have hoM : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I)
      oM.orientation :=
    DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_manifoldOrientation oM
  have hpush : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I)
      (fun y : N => Orientation.map (Fin n) ((mfd (f.symm y)).toLinearEquiv)
        (oM.orientation (f.symm y))) :=
    DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_diffeomorph_map f
      oN.dimension_eq oM.orientation hoM
  obtain ⟨O', hO'⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation I
      oN.dimension_eq
      (fun y : N => Orientation.map (Fin n) ((mfd (f.symm y)).toLinearEquiv)
        (oM.orientation (f.symm y))) hpush
  have hpres : f.preservesOrientation oM O' := by
    intro x
    change Orientation.map (Fin n) ((mfd x).toLinearEquiv) (oM.orientation x) = O'.orientation (f x)
    rw [hO']
    beta_reduce
    rw [f.symm_apply_apply]
  have hO'O : O' = oN := by
    apply DifferentialGeometry.ManifoldOrientation.eq_of_eq_at O' oN (f x₀)
    rw [hO']
    beta_reduce
    rw [f.symm_apply_apply]
    exact h₀'
  rw [← hO'O]
  exact hpres

set_option backward.isDefEq.respectTransparency false in
theorem preservesOrientation_iff_eq_at [PreconnectedSpace N]
    (f : M ≃ₘ⟮I, I⟯ N) (oM : DifferentialGeometry.ManifoldOrientation I M n)
    (oN : DifferentialGeometry.ManifoldOrientation I N n) (x₀ : M) :
    f.preservesOrientation oM oN ↔
      Orientation.map (Fin n)
        ((f.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv)
        (oM.orientation x₀) = oN.orientation (f x₀) :=
  ⟨fun h => h x₀, fun h => preservesOrientation_of_eq_at f oM oN x₀ h⟩

end Diffeomorph
