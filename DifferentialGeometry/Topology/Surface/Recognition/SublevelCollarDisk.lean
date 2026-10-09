import DifferentialGeometry.Topology.Surface.Recognition.DiskCollarGluing
import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBand

/-!
# A topological-disk sublevel stays a disk across a regular band (SF6, step 1)

Let `f` be smooth on an open set `W` of a boundaryless manifold, with a smooth field `Y` on `W` such
that `df(Y) > 0` on the compact band `f⁻¹[s, s']`.  Lane LC46's `exists_field_band_product_of_contMDiffOn`
gives product coordinates `{f = s} × [s, s'] ≃ₜ f⁻¹[s, s']`.  If the sublevel `{f ≤ s}` is a topological
disk with boundary sphere `{f = s}`, attaching this collar (`exists_disk_of_disk_union_collar`) shows that
`{f ≤ s'}` is a topological disk with boundary sphere `{f = s'}`.
-/

set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [T2Space Z] [SigmaCompactSpace Z]

/-- **SF6, step 1.** Across a band `f⁻¹[s, s']` carrying a smooth field with `df(Y) > 0`, a
topological-disk sublevel `{f ≤ s}` with boundary `{f = s}` extends to the topological disk
`{f ≤ s'}` with boundary `{f = s'}`. -/
theorem exists_disk_sublevel_of_field {m : ℕ} {f : Z → ℝ} (hf : Continuous f) {W : Set Z}
    (hW : IsOpen W) (hfW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f W) {s s' : ℝ} (hss' : s < s')
    (hK : IsCompact (f ⁻¹' Icc s s')) (hKW : f ⁻¹' Icc s s' ⊆ W)
    (Y : (x : Z) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I Z)) W)
    (hpos : ∀ x ∈ f ⁻¹' Icc s s', 0 < mvfderiv (I := I) f x (Y x))
    {φ : Disk (m + 1) → Z} (hφ : Continuous φ) (hφ' : Injective φ)
    (hrange : range φ = {x | f x ≤ s}) (hbd : φ '' diskSphere (m + 1) = {x | f x = s}) :
    ∃ φ' : Disk (m + 1) → Z, Continuous φ' ∧ Injective φ' ∧ range φ' = {x | f x ≤ s'} ∧
      φ' '' diskSphere (m + 1) = {x | f x = s'} := by
  have hsmem : s ∈ Icc s s' := ⟨le_refl s, hss'.le⟩
  obtain ⟨-, -, -, -, -, -, -, -, e, -, -, hes2, heh, hebase⟩ :=
    exists_field_band_product_of_contMDiffOn hf hW hfW hss' hsmem hK hKW Y hY hpos
  have hlev : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      f (φ ⟨θ, sphere_subset_closedBall θ.2⟩) = s := by
    intro θ
    have : φ ⟨θ, sphere_subset_closedBall θ.2⟩ ∈ φ '' diskSphere (m + 1) :=
      mem_image_of_mem φ (mem_diskSphere.mpr (mem_sphere_zero_iff_norm.mp θ.2))
    rw [hbd] at this
    exact this
  have hd : 0 < s' - s := sub_pos.mpr hss'
  let base : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → {x : Z // f x = s} := fun θ =>
    ⟨φ ⟨θ, sphere_subset_closedBall θ.2⟩, hlev θ⟩
  let hgt : Icc (0 : ℝ) 1 → Icc s s' := fun t =>
    ⟨s + t * (s' - s), by
      constructor
      · nlinarith [t.2.1]
      · nlinarith [t.2.2]⟩
  let c : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Icc (0 : ℝ) 1 → Z := fun w =>
    (e (base w.1, hgt w.2) : Z)
  have hfc : ∀ w, f (c w) = s + (w.2 : ℝ) * (s' - s) := fun w => heh (base w.1, hgt w.2)
  have hc : Continuous c := by
    refine continuous_subtype_val.comp (e.continuous.comp (Continuous.prodMk ?_ ?_))
    · exact (hφ.comp ((continuous_subtype_val.comp continuous_fst).subtype_mk _)).subtype_mk _
    · exact ((continuous_const.add ((continuous_subtype_val.comp continuous_snd).mul
        continuous_const))).subtype_mk _
  have hc' : Injective c := by
    intro a b hab
    have h1 := e.injective (Subtype.ext hab)
    simp only [Prod.mk.injEq] at h1
    refine Prod.ext ?_ ?_
    · have h2 := congrArg Subtype.val h1.1
      have h3 := hφ' h2
      have h4 := congrArg Subtype.val h3
      exact Subtype.ext h4
    · have h2 := congrArg Subtype.val h1.2
      simp only [hgt] at h2
      have h4 : (a.2 : ℝ) = b.2 := by
        have := mul_right_cancel₀ hd.ne' (add_left_cancel h2)
        exact this
      exact Subtype.ext h4
  have hmatch : ∀ (θ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : Icc (0 : ℝ) 1)
      (z : Disk (m + 1)), (t : ℝ) = 0 → (z : EuclideanSpace ℝ (Fin (m + 1))) = θ → c (θ, t) = φ z := by
    intro θ t z ht hz
    have hz' : z = ⟨θ, sphere_subset_closedBall θ.2⟩ := Subtype.ext hz
    have ht' : hgt t = ⟨s, hsmem⟩ := Subtype.ext (by simp [hgt, ht])
    simp only [c, ht', hebase, hz']
    rfl
  have hinter : ∀ z w, φ z = c w → (w.2 : ℝ) = 0 := by
    intro z w hzw
    have h1 : f (φ z) ≤ s := by
      have : φ z ∈ range φ := mem_range_self z
      rw [hrange] at this
      exact this
    rw [hzw, hfc] at h1
    have h2 : (w.2 : ℝ) * (s' - s) ≤ 0 := by linarith
    have h3 : (w.2 : ℝ) ≤ 0 := by nlinarith
    exact le_antisymm h3 w.2.2.1
  obtain ⟨φ', hφc, hφi, hφr, hφb⟩ := exists_disk_of_disk_union_collar hφ hφ' hc hc' hmatch hinter
  -- every point of the band is on the collar
  have hband : ∀ y : Z, f y ∈ Icc s s' →
      ∃ w, c w = y := by
    intro y hy
    obtain ⟨⟨x, τ⟩, hxτ⟩ := e.surjective ⟨y, hy⟩
    have hx : x.1 ∈ φ '' diskSphere (m + 1) := by rw [hbd]; exact x.2
    obtain ⟨z, hz, hzx⟩ := hx
    let θ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
      ⟨z, mem_sphere_zero_iff_norm.mpr (mem_diskSphere.mp hz)⟩
    let t : Icc (0 : ℝ) 1 := ⟨((τ : ℝ) - s) / (s' - s), by
      constructor
      · exact div_nonneg (by linarith [τ.2.1]) hd.le
      · rw [div_le_one hd]; linarith [τ.2.2]⟩
    refine ⟨(θ, t), ?_⟩
    have hb : base θ = x := Subtype.ext (by simp only [base]; rw [← hzx])
    have ht : hgt t = τ := Subtype.ext (by
      simp only [hgt, t]
      field_simp
      ring)
    simp only [c, hb, ht, hxτ]
  refine ⟨φ', hφc, hφi, ?_, ?_⟩
  · rw [hφr, hrange]
    apply Subset.antisymm
    · rintro y (hy | ⟨w, rfl⟩)
      · exact le_trans hy hss'.le
      · change f (c w) ≤ s'
        rw [hfc]
        nlinarith [w.2.2.2]
    · intro y hy
      by_cases hys : f y ≤ s
      · exact Or.inl hys
      · obtain ⟨w, rfl⟩ := hband y ⟨(not_le.mp hys).le, hy⟩
        exact Or.inr ⟨w, rfl⟩
  · rw [hφb]
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      change f (c w) = s'
      rw [hfc, show (w.2 : ℝ) = 1 from hw]
      ring
    · intro y hy
      have hy' : f y = s' := hy
      obtain ⟨w, rfl⟩ := hband y ⟨by linarith, hy'.le⟩
      refine ⟨w, ?_, rfl⟩
      change (w.2 : ℝ) = 1
      rw [hfc] at hy'
      have : (w.2 : ℝ) * (s' - s) = 1 * (s' - s) := by linarith
      exact mul_right_cancel₀ hd.ne' this

end DifferentialGeometry.Topology.Surface
