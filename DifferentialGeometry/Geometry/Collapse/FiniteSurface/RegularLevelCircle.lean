import DifferentialGeometry.Topology.Surface.Recognition.SublevelSmoothDisk

/-!
# A compact connected regular level of a surface function is a Jordan circle

`exists_circle_of_regular_level`: on a boundaryless surface, a function smooth on an open set `W`
containing a compact connected level `{f = s}` at which its differential does not vanish has that
level as the image of a continuous injective map of the circle (lane N1's regular-fibre circle,
applied on the open submanifold `W`, as in SF-C's `exists_smooth_disk_of_sublevel`, step 3).
Consumer: LFR23's distance levels (through a smooth cross-section) and LFR24's core levels.
-/

set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]

/-- **A regular compact connected level is a Jordan circle.** -/
theorem exists_circle_of_regular_level [T2Space Z] (hE : Module.finrank ℝ E = 2) {f : Z → ℝ}
    {W : TopologicalSpace.Opens Z} (hfW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f W) {s : ℝ}
    (hsub : ∀ y, f y = s → y ∈ W)
    (hdf : ∀ y, f y = s → ∃ v, mvfderiv (I := I) f y v ≠ 0)
    (hcpt : IsCompact {x | f x = s}) (hconn : IsConnected {x | f x = s}) :
    ∃ c : Circle → Z, Continuous c ∧ Injective c ∧ range c = {x | f x = s} := by
  let fW : W → ℝ := fun x => f x
  have hfWs : ContMDiff I 𝓘(ℝ, ℝ) ∞ fW := hfW.comp_contMDiff contMDiff_subtype_val fun x => x.2
  have hLreg : ∀ x : W, fW x = s → Surjective (mfderiv I 𝓘(ℝ, ℝ) fW x) := fun x hx =>
    DifferentialGeometry.Topology.Surface.surjective_mfderiv_restrict_opens hfW x (hdf x hx)
  have hLimage : (Subtype.val : W → Z) '' {x : W | fW x = s} = {x | f x = s} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hsub y hy⟩, hy, rfl⟩
  have hLcpt : IsCompact {x : W | fW x = s} := by
    rw [Subtype.isCompact_iff, hLimage]
    exact hcpt
  have hLconn : IsConnected {x : W | fW x = s} := by
    have hind : Topology.IsInducing (Subtype.val : W → Z) := Topology.IsInducing.subtypeVal
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := hconn.nonempty
      exact ⟨⟨y, hsub y hy⟩, hy⟩
    · apply hind.isPreconnected_image.mp
      rw [hLimage]
      exact hconn.isPreconnected
  obtain ⟨Dc⟩ := DifferentialGeometry.Topology.Manifold.OneManifold.nonempty_circle_diffeomorph_regularFiber
    fW s hfWs hLreg (by simp [hE]) hLcpt hLconn
  let _ : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) {x : W // fW x = s} :=
    DifferentialGeometry.Topology.Manifold.regularFiberChartedSpace fW s hfWs hLreg
  refine ⟨fun z => ((Dc z : {x : W // fW x = s}) : W), ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (continuous_subtype_val.comp Dc.continuous)
  · intro z z' hzz'
    exact Dc.injective (Subtype.ext (Subtype.ext hzz'))
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (Dc z).2
    · intro hy
      obtain ⟨z, hz⟩ := Dc.surjective ⟨⟨y, hsub y hy⟩, hy⟩
      refine ⟨z, ?_⟩
      exact congrArg (fun w : {x : W // fW x = s} => ((w : W) : Z)) hz

end DifferentialGeometry.Geometry.Collapse
