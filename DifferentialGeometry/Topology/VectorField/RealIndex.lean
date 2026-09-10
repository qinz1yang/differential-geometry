import DifferentialGeometry.Topology.LocalDegree.RealCoordinateChange
import DifferentialGeometry.Topology.VectorField.Transport

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) 1 M]

structure ContinuousIsolatedZero (V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x) (x : M) : Prop where
  zero : V x = 0
  continuous : ∃ s ∈ 𝓝 x,
    ContinuousOn (fun y ↦ (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, ℝ) M)) s
  isolated : ∀ᶠ y in 𝓝 x, V y = 0 → y = x


def realIndexChart (x : M) : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) M ℝ 1 where
  toPartialEquiv := (chartAt ℝ x).toPartialEquiv
  open_source := (chartAt ℝ x).open_source
  open_target := (chartAt ℝ x).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

private theorem continuousOn_real_section {P : ℝ → ℝ} {s : Set ℝ}
    (hc : ContinuousOn (fun y ↦ (⟨y, P y⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) s) :
    ContinuousOn P s := by
  intro y hy
  have hh := (FiberBundle.continuousWithinAt_section ℝ).mp (hc y hy)
  simpa only [trivializationAt_model_space_apply] using! hh

theorem ContinuousIsolatedZero.real_pullback {n : ℕ∞ω}
    {V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x}
    (f : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ M n) (hn : 1 ≤ n)
    {a : ℝ} (ha : a ∈ f.source) (hV : ContinuousIsolatedZero V (f a)) :
    Poincare.LocalDegree.realIsolatedZero
      (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f V) a := by
  obtain ⟨s, hs, hc⟩ := hV.continuous
  obtain ⟨U, hUs, hU, haU⟩ := mem_nhds_iff.mp hs
  let t : Set ℝ := f.source ∩ f ⁻¹' U
  have ht : t ∈ 𝓝 a := inter_mem (f.open_source.mem_nhds ha)
    ((f.toOpenPartialHomeomorph.continuousAt ha).preimage_mem_nhds (hU.mem_nhds haU))
  have hP : ContinuousOn
      (fun y ↦ (⟨y, _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f V y⟩ :
        TangentBundle 𝓘(ℝ, ℝ) ℝ)) t := by
    intro y hy
    have hVy : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 0
        (fun z ↦ (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, ℝ) M)) (f y) :=
      (contMDiffOn_zero_iff.mpr (hc.mono hUs)).contMDiffAt (hU.mem_nhds hy.2)
    exact (contMDiffAt_mpullback_partialDiffeomorph f (by simpa using hn) hy.1 hVy).continuousAt.continuousWithinAt
  apply Poincare.LocalDegree.realIsolatedZero_of_nhds ht (continuousOn_real_section hP)
  · exact (mpullback_partialDiffeomorph_eq_zero_iff f
      (ne_of_gt (zero_lt_one.trans_le hn)) V ha).mpr hV.zero
  · apply eventually_nhdsWithin_iff.mpr
    have hi := (mpullback_partialDiffeomorph_isolated_iff f
      (ne_of_gt (zero_lt_one.trans_le hn)) V ha).mpr hV.isolated
    filter_upwards [hi] with y hy
    exact fun hne hz ↦ hne (hy hz)


theorem ContinuousIsolatedZero.in_coordinates
    {V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x} {x : M}
    (hV : ContinuousIsolatedZero V x) {n : ℕ∞ω}
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) M ℝ n) (hn : 1 ≤ n)
    (hx : x ∈ c.source) :
    Poincare.LocalDegree.realIsolatedZero
      (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) c.symm V) (c x) := by
  apply ContinuousIsolatedZero.real_pullback c.symm hn (c.map_source hx)
  exact (c.left_inv hx).symm ▸ hV

omit [IsManifold 𝓘(ℝ, ℝ) 1 M] in
private theorem real_mpullback_congr {f g : ℝ → M}
    (V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x) {a : ℝ} (h : f =ᶠ[𝓝 a] g) :
    _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f V a =
      _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g V a := by
  unfold _root_.VectorField.mpullback
  erw [h.mfderiv_eq, h.eq_of_nhds]

omit [IsManifold 𝓘(ℝ, ℝ) 1 M] in
private theorem real_mpullback_comp {f : ℝ → ℝ} {g : ℝ → M}
    (V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x) {a : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f a)
    (hg : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g (f a))
    (hi : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g (f a)).IsInvertible) :
    _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (g ∘ f) V a =
      _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f
        (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) g V) a := by
  simp only [_root_.VectorField.mpullback, mfderiv_comp _ hg hf, Function.comp_apply]
  exact hi.inverse_comp_apply_of_left

theorem realLocalDegree_in_coordinates_eq
    {V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x} {x : M}
    (hV : ContinuousIsolatedZero V x)
    (c d : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) M ℝ 1)
    (hcx : x ∈ c.source) (hdx : x ∈ d.source) :
    Poincare.LocalDegree.realLocalDegree
        (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) c.symm V) (c x)
        (hV.in_coordinates c le_rfl hcx) =
      Poincare.LocalDegree.realLocalDegree
        (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) d.symm V) (d x)
        (hV.in_coordinates d le_rfl hdx) := by
  let f := d.symm.trans c
  have hxf : d x ∈ f.source := by
    refine ⟨d.map_source hdx, ?_⟩
    change d.toPartialEquiv.symm (d x) ∈ c.source
    rw [d.left_inv hdx]
    exact hcx
  have hcenter : f (d x) = c x := congrArg c (d.left_inv hdx)
  have hmap : (c.symm ∘ f : ℝ → M) =ᶠ[𝓝 (d x)] d.symm := by
    filter_upwards [f.open_source.mem_nhds hxf] with y hy
    exact c.left_inv hy.2
  have hfields :
      _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) d.symm V =ᶠ[𝓝 (d x)]
        _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f
          (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) c.symm V) := by
    filter_upwards [hmap.eventuallyEq_nhds, f.open_source.mem_nhds hxf] with y hy hys
    exact (real_mpullback_congr V hy).symm.trans
      (real_mpullback_comp V (f.mdifferentiableAt one_ne_zero hys)
        (c.symm.mdifferentiableAt one_ne_zero (c.map_source hys.2))
        (isInvertible_mfderiv_partialDiffeomorph c.symm one_ne_zero (c.map_source hys.2)))
  have hc := hV.in_coordinates c le_rfl hcx
  have hd := hV.in_coordinates d le_rfl hdx
  have hcf : Poincare.LocalDegree.realIsolatedZero
      (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) c.symm V) (f (d x)) :=
    hcenter.symm ▸ hc
  have hp := Poincare.LocalDegree.realIsolatedZero_mpullback_partialDiffeomorph f le_rfl hxf hcf
  have hdegree := Poincare.LocalDegree.realLocalDegree_mpullback_partialDiffeomorph f le_rfl hxf hcf
  have hsame := Poincare.LocalDegree.realLocalDegree_congr hd hp hfields
  exact (hsame.trans (by simpa only [hcenter] using hdegree)).symm

def realIndex (V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x) (x : M)
    (hV : ContinuousIsolatedZero V x) : ℤ :=
  Poincare.LocalDegree.realLocalDegree
    (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (realIndexChart x).symm V)
    (realIndexChart x x)
    (hV.in_coordinates (realIndexChart x) le_rfl (mem_chart_source ℝ x))


theorem realIndex_eq_in_coordinates
    {V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x} {x : M}
    (hV : ContinuousIsolatedZero V x)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) M ℝ 1) (hx : x ∈ c.source) :
    realIndex V x hV =
      Poincare.LocalDegree.realLocalDegree
        (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) c.symm V) (c x)
        (hV.in_coordinates c le_rfl hx) :=
  realLocalDegree_in_coordinates_eq hV (realIndexChart x) c (mem_chart_source ℝ x) hx


theorem realIndex_eq_realLocalDegree
    {V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x}
    (f : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ M 1) {a : ℝ}
    (ha : a ∈ f.source) (hV : ContinuousIsolatedZero V (f a)) :
    realIndex V (f a) hV =
      Poincare.LocalDegree.realLocalDegree
        (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f V) a
        (hV.real_pullback f le_rfl ha) := by
  have hh := realIndex_eq_in_coordinates hV f.symm (f.map_source ha)
  change realIndex V (f a) hV =
    Poincare.LocalDegree.realLocalDegree
      (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f V)
      (f.toPartialEquiv.symm (f a)) _ at hh
  simpa only [f.left_inv ha] using hh

theorem realIndex_smul_generator
    {V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x} {x : M}
    (hV : ContinuousIsolatedZero V x)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) M ℝ 1) (hx : x ∈ c.source)
    {R : ℝ} (hR : Poincare.LocalDegree.RealIsolatingRadius
      (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) c.symm V) (c x) R)
    (r : Ioc (0 : ℝ) R) :
    realIndex V x hV • Poincare.LocalDegree.zeroSphereGenerator =
      Poincare.LocalDegree.zeroSphereReducedMap
        (Poincare.LocalDegree.sphereMap
          (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) c.symm V) (c x) R
          hR.continuousOn hR.nonzero r) Poincare.LocalDegree.zeroSphereGenerator := by
  rw [realIndex_eq_in_coordinates hV c hx]
  exact Poincare.LocalDegree.realLocalDegree_smul_generator _ hR r

theorem realIndex_eq_sign_of_hasDerivAt
    {V : ∀ x : M, TangentSpace 𝓘(ℝ, ℝ) x}
    (f : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ M 1) {a d : ℝ}
    (ha : a ∈ f.source) (hV : ContinuousIsolatedZero V (f a))
    (hd : HasDerivAt (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f V) d a)
    (hne : d ≠ 0) : realIndex V (f a) hV = (SignType.sign d : ℤ) :=
  (realIndex_eq_realLocalDegree f ha hV).trans
    (Poincare.LocalDegree.realLocalDegree_eq_sign_of_hasDerivAt _ hd hne)

end Poincare.VectorField
