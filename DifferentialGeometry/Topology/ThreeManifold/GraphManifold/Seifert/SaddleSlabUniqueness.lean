import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlab
import DifferentialGeometry.Topology.Ehresmann.BoundaryInterval
import DifferentialGeometry.Topology.Ehresmann.Interval
import DifferentialGeometry.Topology.Morse.NormalForm.Manifold
import DifferentialGeometry.Topology.Morse.Rearrangement.NegDual

/-!
# One-saddle slabs and planar pieces

Packet RG03b. Tier 1, no critical point: `circleIccAnnulus` identifies `S¹ × [0, 1]` with the
K06b annulus `planarSet 2` by `(t, s) ↦ (1/2 + 5 s / 2) t`, so the inner circle (collar `1`) is
`s = 0` and the outer one (collar `0`) is `s = 1`. Let `M` be compact with smooth boundary and `g`
a function on it without critical points whose boundary lies in `g ⁻¹' {a, b}`. The trivialization
`exists_boundary_interval_trivialization` together with a parametrisation of the level `a` by the
circle gives `exists_annulus_diffeomorph_of_regularSlab`: the slab is the annulus, `g` is affine
in the radius, collar `1` lies on level `a` and collar `0` on level `b`. For a connected slab
the circle parametrisation follows from `CircleClassification` (a compact connected
boundaryless one-manifold is a circle), a named Prop that records this missing
classification. For a function `f` on a boundaryless surface with regular values `a < b`, the
set `slabSet f a b = {(f - a) (f - b) ≤ 0} = f ⁻¹' Icc a b` is a surface with boundary
(`slabAtlas`, the regular sublevel atlas) whose boundary is `f ⁻¹' {a, b}`; for it,
`exists_annulus_of_surfaceSlab` is tier 1.

Tier 2: `exists_saddleChart_two` is the Morse lemma at an index-one critical point of a surface,
`f (Φ y) = f p + (y₁² - y₀²) / 2` on a ball.

Tier 3, conditional: `OneSaddleSlabUniqueness` is a named Prop. It asserts the following for any
two compact connected slabs between regular levels, each containing a single critical point
(nondegenerate, of index one) and each with a disconnected lower level: they are diffeomorphic by
a map sending the lower level to the lower level and the upper level to the upper level. Apply it
with the model `pantsHeight` of `SaddleSlab.lean`, whose lower level is the pair of hole circles
and whose slab is `planarSet 3` up to the identity (`pantsSlabDiffeomorph`). This gives
`exists_planarBase_of_saddleSlab`: the slab is `pantsPlanarBase`, with collars `1, 2` on level `a`
and collar `0` on level `b`. `exists_planarBase_of_saddleSlab_upper` is the reverse incidence
(two upper circles), obtained through `-f`.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology.Morse.CellAttachment
open scoped Manifold ContDiff Topology

universe w uE uH uM uN uN'

namespace GC.Seifert

def annulusRadius (s : ℝ) : ℝ := 1 / 2 + 5 / 2 * s

theorem norm_annulusRadius_smul (s : Icc (0 : ℝ) 1) (t : Circle) :
    ‖(annulusRadius s.1 : ℝ) • (t : ℂ)‖ = annulusRadius s.1 := by
  have hs := s.2.1
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg]
  unfold annulusRadius
  linarith

theorem annulus_norm_bounds (x : planarSet.{w} 2) :
    1 / 2 ≤ ‖x.val.down‖ ∧ ‖x.val.down‖ ≤ 3 := by
  have h := (mem_planarSet_iff (Or.inl rfl) x.val).mp x.2
  rw [mem_planarModel_two] at h
  exact ⟨h.2, h.1⟩

def circleIccAnnulusMap (p : Circle × Icc (0 : ℝ) 1) : planarSet.{w} 2 :=
  ⟨ULift.up ((annulusRadius p.2.1 : ℝ) • (p.1 : ℂ)), by
    rw [mem_planarSet_iff (Or.inl rfl), mem_planarModel_two]
    change ‖(annulusRadius p.2.1 : ℝ) • (p.1 : ℂ)‖ ≤ 3 ∧
      1 / 2 ≤ ‖(annulusRadius p.2.1 : ℝ) • (p.1 : ℂ)‖
    rw [norm_annulusRadius_smul]
    unfold annulusRadius
    constructor <;> linarith [p.2.2.1, p.2.2.2]⟩

def annulusLevel (x : planarSet.{w} 2) : ℝ := 2 / 5 * (‖x.val.down‖ - 1 / 2)

theorem annulusLevel_mem (x : planarSet.{w} 2) : annulusLevel x ∈ Icc (0 : ℝ) 1 := by
  have h := annulus_norm_bounds x
  unfold annulusLevel
  constructor <;> linarith [h.1, h.2]

def annulusCircleIccMap (x : planarSet.{w} 2) : Circle × Icc (0 : ℝ) 1 :=
  (unitOf x.val.down, ⟨annulusLevel x, annulusLevel_mem x⟩)

theorem annulus_down_ne_zero (x : planarSet.{w} 2) : x.val.down ≠ 0 := by
  have h := (annulus_norm_bounds x).1
  intro h0
  rw [h0, norm_zero] at h
  norm_num at h

theorem contMDiff_annulusLevel : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ (annulusLevel.{w}) := by
  intro x
  have hn : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ (fun x : planarSet.{w} 2 => ‖x.val.down‖) x :=
    (contDiffAt_norm ℝ (annulus_down_ne_zero x)).contMDiffAt.comp x
      (contMDiff_planarSet_down 2 x)
  exact ((contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff.contMDiffAt).comp x hn

def circleIccAnnulus :
    (Circle × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 1).prod (𝓡∂ 1), 𝓡∂ 2⟯ planarSet.{w} 2 where
  toFun := circleIccAnnulusMap
  invFun := annulusCircleIccMap
  left_inv p := by
    have hr : 0 < annulusRadius p.2.1 := by
      unfold annulusRadius
      linarith [p.2.2.1]
    refine Prod.ext (unitOf_smul hr p.1) (Subtype.ext ?_)
    change annulusLevel.{w} (circleIccAnnulusMap.{w} p) = p.2.1
    unfold annulusLevel
    change 2 / 5 * (‖(annulusRadius p.2.1 : ℝ) • (p.1 : ℂ)‖ - 1 / 2) = p.2.1
    rw [norm_annulusRadius_smul]
    unfold annulusRadius
    ring
  right_inv x := by
    apply Subtype.ext
    apply ULift.ext
    change (annulusRadius (annulusLevel x) : ℝ) • (unitOf x.val.down : ℂ) = x.val.down
    have h : annulusRadius (annulusLevel x) = ‖x.val.down‖ := by
      unfold annulusRadius annulusLevel
      ring
    rw [h, norm_smul_unitOf]
  contMDiff_toFun := by
    refine ((planarAtlas 2).contMDiff_iff_subtype_val _).mpr ?_
    have hs : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : Circle × Icc (0 : ℝ) 1 => annulusRadius p.2.1) :=
      (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
    have ht : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ) ∞
        (fun p : Circle × Icc (0 : ℝ) 1 => (p.1 : ℂ)) :=
      contMDiff_circle_coe.comp contMDiff_fst
    exact contMDiff_planeLift_up.comp (hs.smul ht)
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ ?_
    · exact contMDiffOn_unitOf.comp_contMDiff (contMDiff_planarSet_down 2)
        fun x => annulus_down_ne_zero x
    · refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨?_, contMDiff_annulusLevel⟩
      exact contMDiff_annulusLevel.continuous.subtype_mk _

theorem circleIccAnnulus_symm_snd (x : planarSet.{w} 2) :
    ((circleIccAnnulus.{w}.symm x).2 : ℝ) = annulusLevel x :=
  rfl

theorem annulusLevel_collar_zero (t : Circle) :
    annulusLevel (annulusPlanarBase.{w}.collar 0 (t, halfZero)) = 1 := by
  unfold annulusLevel
  have h := annulusPlanarBase.{w}.embedding_collar 0 t
  have hn := norm_planarCircleMap_sub 2 0 t
  change (annulusPlanarBase.{w}.collar 0 (t, halfZero)).val.down = _ at h
  rw [h]
  simp only [planarCenter, planarRadius] at hn
  norm_num at hn
  rw [hn]
  norm_num

theorem annulusLevel_collar_one (t : Circle) :
    annulusLevel (annulusPlanarBase.{w}.collar 1 (t, halfZero)) = 0 := by
  unfold annulusLevel
  have h := annulusPlanarBase.{w}.embedding_collar 1 t
  have hn := norm_planarCircleMap_sub 2 1 t
  change (annulusPlanarBase.{w}.collar 1 (t, halfZero)).val.down = _ at h
  rw [h]
  simp only [planarCenter, planarRadius] at hn
  norm_num at hn
  rw [hn]
  norm_num


def CircleClassification : Prop :=
  ∀ (E : Type uE) (H : Type uH) (F : Type uM) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace F] [ChartedSpace H F]
    (J : ModelWithCorners ℝ E H) [J.Boundaryless] [IsManifold J ∞ F] [T2Space F]
    [CompactSpace F] [ConnectedSpace F], Module.finrank ℝ E = 1 → Nonempty (Circle ≃ₘ⟮𝓡 1, J⟯ F)

section Slab

variable {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [CompactSpace M] [T2Space M] {I : ModelWithCorners ℝ E H}
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem exists_annulus_diffeomorph_of_regularSlab {g : M → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hreg : ∀ x, mfderiv I 𝓘(ℝ) g x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → g x = a ∨ g x = b)
    (ha : a ∈ range g) (hb : b ∈ range g)
    (η : Circle ≃ₘ⟮𝓡 1, hI.boundaryI⟯ boundaryLevel g a b hab.ne hg.continuous hboundary) :
    ∃ e : planarSet.{w} 2 ≃ₘ⟮𝓡∂ 2, I⟯ M,
      (∀ x, g (e x) = a + (b - a) * annulusLevel x) ∧
      (∀ t, g (e (annulusPlanarBase.{w}.collar 1 (t, halfZero))) = a) ∧
      ∀ t, g (e (annulusPlanarBase.{w}.collar 0 (t, halfZero))) = b := by
  have : Fact (a < b) := ⟨hab⟩
  obtain ⟨Θ, hh, -⟩ := exists_boundary_interval_trivialization hab hg hreg hboundary ha hb
  let Ψ := unitCylinderDiffeomorphOfProduct a b η Θ
  have hΨ : ∀ x, g ((circleIccAnnulus.{w}.symm.trans Ψ) x) = a + (b - a) * annulusLevel x := by
    intro x
    change g (Ψ (circleIccAnnulus.symm x)) = _
    rw [unitCylinderDiffeomorphOfProduct_apply, hh, affineIntervalDiffeomorph_apply,
      circleIccAnnulus_symm_snd]
    ring
  refine ⟨circleIccAnnulus.symm.trans Ψ, hΨ, fun t => ?_, fun t => ?_⟩
  · have h := hΨ (annulusPlanarBase.{w}.collar 1 (t, halfZero))
    rw [annulusLevel_collar_one] at h
    linarith
  · have h := hΨ (annulusPlanarBase.{w}.collar 0 (t, halfZero))
    rw [annulusLevel_collar_zero] at h
    linarith

theorem exists_annulus_diffeomorph_of_connected_regularSlab
    (hcirc : CircleClassification.{uE, uH, uM}) (hdim : Module.finrank ℝ E = 2)
    [ConnectedSpace M] {g : M → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hreg : ∀ x, mfderiv I 𝓘(ℝ) g x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → g x = a ∨ g x = b)
    (ha : a ∈ range g) (hb : b ∈ range g) :
    ∃ e : planarSet.{w} 2 ≃ₘ⟮𝓡∂ 2, I⟯ M,
      (∀ x, g (e x) = a + (b - a) * annulusLevel x) ∧
      (∀ t, g (e (annulusPlanarBase.{w}.collar 1 (t, halfZero))) = a) ∧
      ∀ t, g (e (annulusPlanarBase.{w}.collar 0 (t, halfZero))) = b := by
  have : Fact (a < b) := ⟨hab⟩
  obtain ⟨Θ, -, -⟩ := exists_boundary_interval_trivialization hab hg hreg hboundary ha hb
  let F := boundaryLevel g a b hab.ne hg.continuous hboundary
  have hc : Continuous fun x : M => (Θ.symm x).1 := continuous_fst.comp Θ.symm.continuous
  have hsurj : Surjective fun x : M => (Θ.symm x).1 := fun y =>
    ⟨Θ (y, ⟨a, le_rfl, hab.le⟩), by simp⟩
  have : CompactSpace F := ⟨by
    rw [← hsurj.range_eq]
    exact isCompact_range hc⟩
  have : ConnectedSpace F := hsurj.connectedSpace hc
  have hdimB : Module.finrank ℝ hI.boundaryE = 1 := by
    have h := hI.finrank_boundaryE_succ
    omega
  obtain ⟨η⟩ := hcirc hI.boundaryE hI.boundaryH F hI.boundaryI hdimB
  exact exists_annulus_diffeomorph_of_regularSlab hab hg hreg hboundary ha hb η

end Slab

section SurfaceSlab

def slabQuadratic (a b t : ℝ) : ℝ := (t - a) * (t - b)

def slabSet {N : Type uN} (f : N → ℝ) (a b : ℝ) : Set N := {x | slabQuadratic a b (f x) ≤ 0}

theorem mem_slabSet_iff {N : Type uN} {f : N → ℝ} {a b : ℝ} (hab : a ≤ b) (x : N) :
    x ∈ slabSet f a b ↔ f x ∈ Icc a b := by
  change (f x - a) * (f x - b) ≤ 0 ↔ _
  constructor
  · intro h
    by_contra hc
    rw [mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

theorem slabSet_eq {N : Type uN} {f : N → ℝ} {a b : ℝ} (hab : a ≤ b) :
    slabSet f a b = f ⁻¹' Icc a b :=
  Set.ext (mem_slabSet_iff hab)

theorem slabQuadratic_eq_zero_iff {a b t : ℝ} : slabQuadratic a b t = 0 ↔ t = a ∨ t = b := by
  unfold slabQuadratic
  rw [mul_eq_zero, sub_eq_zero, sub_eq_zero]

variable {E : Type*} {H : Type*} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [T2Space N] in
theorem contMDiff_slabQuadratic_comp {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (a b : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => slabQuadratic a b (f x)) := by
  have h : ContDiff ℝ ∞ (slabQuadratic a b) := by
    unfold slabQuadratic
    fun_prop
  exact h.contMDiff.comp hf

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [T2Space N] in
theorem mfderiv_slabQuadratic_comp_ne_zero {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) {x : N} (hx : slabQuadratic a b (f x) = 0)
    (hreg : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => slabQuadratic a b (f y)) x ≠ 0 := by
  have hD : HasMFDerivAt I 𝓘(ℝ, ℝ) f x (mfderiv I 𝓘(ℝ, ℝ) f x) :=
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt
  have hd : HasDerivAt (slabQuadratic a b) (2 * f x - a - b) (f x) := by
    have h : HasDerivAt (fun t => (t - a) * (t - b)) (1 * (f x - b) + (f x - a) * 1) (f x) :=
      ((hasDerivAt_id' (f x)).sub_const a).mul ((hasDerivAt_id' (f x)).sub_const b)
    exact h.congr_deriv (by ring)
  have hφ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (slabQuadratic a b) (f x)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (2 * f x - a - b)) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt
  have hc := hφ.comp x hD
  have hne : 2 * f x - a - b ≠ 0 := by
    rcases slabQuadratic_eq_zero_iff.mp hx with h | h <;> rw [h] <;> intro h' <;> linarith
  change mfderiv I 𝓘(ℝ, ℝ) (slabQuadratic a b ∘ f) x ≠ 0
  rw [hc.mfderiv]
  intro h
  apply hreg
  ext v
  let d : ℝ := mfderiv I 𝓘(ℝ, ℝ) f x v
  have hv : d * (2 * f x - a - b) = 0 :=
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) h
  rcases mul_eq_zero.mp hv with h1 | h1
  · exact h1
  · exact absurd h1 hne

def slabAtlas (hdim : Module.finrank ℝ E = 2) {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    SmoothBoundaryAtlas I 2 (slabSet f a b) :=
  SmoothBoundaryAtlas.regularSublevel I (n := 1) hdim (contMDiff_slabQuadratic_comp hf a b) 0
    fun x hx => mfderiv_slabQuadratic_comp_ne_zero hf hab hx
      (hreg x (slabQuadratic_eq_zero_iff.mp hx))

omit [IsManifold I ∞ N] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space N] in
theorem regular_endpoints {f : N → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ x, f x ∈ Icc a b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
  intro x hx
  refine hreg x ?_
  rcases hx with h | h <;> rw [h] <;> exact ⟨by linarith, by linarith⟩

omit [T2Space N] in
theorem slab_isBoundaryPoint {hdim : Module.finrank ℝ E = 2} {f : N → ℝ}
    {hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f} {a b : ℝ} {hab : a < b}
    {hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0} (x : slabSet f a b) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    (𝓡∂ 2).IsBoundaryPoint x ↔ f x = a ∨ f x = b := by
  let := (slabAtlas hdim hf hab hreg).toChartedSpace
  exact (SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff I (n := 1) hdim
    (contMDiff_slabQuadratic_comp hf a b) 0 _ x).trans slabQuadratic_eq_zero_iff

theorem exists_annulus_of_surfaceSlab (hcirc : CircleClassification.{0, 0, uN})
    (hdim : Module.finrank ℝ E = 2) {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hreg : ∀ x, f x ∈ Icc a b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsConnected (f ⁻¹' Icc a b))
    (ha : ∃ x, f x = a) (hb : ∃ x, f x = b) :
    letI := (slabAtlas hdim hf hab (regular_endpoints hab.le hreg)).toChartedSpace
    ∃ e : planarSet.{w} 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f a b,
      (∀ x, f (e x) = a + (b - a) * annulusLevel x) ∧
      (∀ t, f (e (annulusPlanarBase.{w}.collar 1 (t, halfZero))) = a) ∧
      ∀ t, f (e (annulusPlanarBase.{w}.collar 0 (t, halfZero))) = b := by
  let C := slabAtlas hdim hf hab (regular_endpoints hab.le hreg)
  let := C.toChartedSpace
  have := C.isManifold
  have hK := slabSet_eq (f := f) hab.le
  have : CompactSpace (slabSet f a b) := isCompact_iff_compactSpace.mp (hK ▸ hcpt)
  have : ConnectedSpace (slabSet f a b) := isConnected_iff_connectedSpace.mp (hK ▸ hconn)
  have hg : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞ (f ∘ Subtype.val : slabSet f a b → ℝ) :=
    hf.comp C.contMDiff_subtype_val
  have hgreg : ∀ x : slabSet f a b, mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) (f ∘ Subtype.val) x ≠ 0 := by
    intro x h
    have hval : MDifferentiableAt (𝓡∂ 2) I (Subtype.val : slabSet f a b → N) x :=
      C.contMDiff_subtype_val.mdifferentiableAt (by simp)
    rw [mfderiv_comp x (hf.mdifferentiableAt (by simp)) hval] at h
    apply hreg x.val ((mem_slabSet_iff hab.le x.val).mp x.2)
    ext w
    obtain ⟨v, hv⟩ := (C.mfderiv_subtypeVal_bijective x).2 w
    have h' : mfderiv I 𝓘(ℝ, ℝ) f x.val (mfderiv (𝓡∂ 2) I Subtype.val x v) = 0 :=
      congrArg (fun L => L v) h
    rw [← hv]
    exact h'
  have hbd : ∀ x : slabSet f a b, (𝓡∂ 2).IsBoundaryPoint x →
      (f ∘ Subtype.val) x = a ∨ (f ∘ Subtype.val) x = b := by
    intro x hx
    exact (slab_isBoundaryPoint x).mp hx
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  have ha' : a ∈ range (f ∘ Subtype.val : slabSet f a b → ℝ) :=
    ⟨⟨xa, (mem_slabSet_iff hab.le xa).mpr ⟨hxa.ge, hxa ▸ hab.le⟩⟩, hxa⟩
  have hb' : b ∈ range (f ∘ Subtype.val : slabSet f a b → ℝ) :=
    ⟨⟨xb, (mem_slabSet_iff hab.le xb).mpr ⟨hxb ▸ hab.le, hxb.le⟩⟩, hxb⟩
  exact exists_annulus_diffeomorph_of_connected_regularSlab hcirc (finrank_euclideanSpace_fin)
    hab hg hgreg hbd ha' hb'

end SurfaceSlab

def OneSaddleSlabUniqueness : Prop :=
  ∀ (E H : Type) (N : Type uN) (E' H' : Type) (N' : Type uN')
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    [TopologicalSpace N'] [ChartedSpace H' N'] [T2Space N']
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ N]
    (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless] [IsManifold I' ∞ N']
    (hdim : Module.finrank ℝ E = 2) (hdim' : Module.finrank ℝ E' = 2)
    (f : N → ℝ) (f' : N' → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf' : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f') (a b a' b' : ℝ) (hab : a < b) (hab' : a' < b')
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hreg' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv I' 𝓘(ℝ, ℝ) f' x ≠ 0) (p : N) (p' : N'),
    f p ∈ Ioo a b → f' p' ∈ Ioo a' b' →
    IsNondegenerateCriticalPointAt I f p → IsNondegenerateCriticalPointAt I' f' p' →
    sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = 1 →
    sigNeg (chartHessianAt (fun y => f' ((extChartAt I' p').symm y)) (extChartAt I' p' p')) = 1 →
    (∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p) →
    (∀ x, f' x ∈ Icc a' b' → IsCriticalPointAt I' f' x → x = p') →
    IsCompact (f ⁻¹' Icc a b) → IsCompact (f' ⁻¹' Icc a' b') →
    IsConnected (f ⁻¹' Icc a b) → IsConnected (f' ⁻¹' Icc a' b') →
    ¬ IsPreconnected (f ⁻¹' {a}) → ¬ IsPreconnected (f' ⁻¹' {a'}) →
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    letI := (slabAtlas hdim' hf' hab' hreg').toChartedSpace
    ∃ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f' a' b',
      ∀ x : slabSet f a b, (f x = a ↔ f' (e x) = a') ∧ (f x = b ↔ f' (e x) = b')

theorem pantsHeight_regular_endpoints :
    ∀ z : ℂ, pantsHeight z = 0 ∨ pantsHeight z = 1 →
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) pantsHeight z ≠ 0 := by
  intro z hz h
  have hmem : pantsHeight z ∈ Icc (0 : ℝ) 1 := by
    rcases hz with h' | h' <;> rw [h'] <;> norm_num
  have h0 : z = 0 := (isCriticalPointAt_pantsHeight_iff hmem).mp h
  rw [h0, pantsHeight_zero] at hz
  norm_num at hz

theorem not_isPreconnected_pantsHeight_zero : ¬ IsPreconnected (pantsHeight ⁻¹' {0}) := by
  intro h
  have him := h.image Complex.re Complex.continuous_re.continuousOn
  have h1 : (1 : ℝ) ∈ Complex.re '' (pantsHeight ⁻¹' {0}) :=
    ⟨1, by norm_num [pantsHeight, pantsLower, pantsUpper], by simp⟩
  have hm1 : (-1 : ℝ) ∈ Complex.re '' (pantsHeight ⁻¹' {0}) :=
    ⟨-1, by norm_num [pantsHeight, pantsLower, pantsUpper], by simp⟩
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨z, hz, hre⟩ := him.Icc_subset hm1 h1 h0
  have hL := (pantsHeight_eq_zero_iff_pantsLower z).mp hz
  unfold pantsLower at hL
  rw [hre] at hL
  nlinarith [sq_nonneg z.im]

abbrev pantsSlabAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 (slabSet pantsHeight 0 1) :=
  slabAtlas Complex.finrank_real_complex contDiff_pantsHeight.contMDiff zero_lt_one
    pantsHeight_regular_endpoints

theorem mem_planarSet_of_mem_pantsSlab (x : slabSet pantsHeight 0 1) :
    ULift.up.{w} x.val ∈ planarSet.{w} 3 :=
  (mem_planarSet_iff (Or.inr rfl) _).mpr
    ((pantsHeight_mem_Icc_iff _).mp ((mem_slabSet_iff zero_le_one _).mp x.2))

theorem mem_pantsSlab_of_mem_planarSet (y : planarSet.{w} 3) :
    y.val.down ∈ slabSet pantsHeight 0 1 :=
  (mem_slabSet_iff zero_le_one _).mpr
    ((pantsHeight_mem_Icc_iff _).mpr ((mem_planarSet_iff (Or.inr rfl) _).mp y.2))

def pantsSlabDiffeomorph :
    letI := pantsSlabAtlas.toChartedSpace
    slabSet pantsHeight 0 1 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ planarSet.{w} 3 :=
  letI := pantsSlabAtlas.toChartedSpace
  { toFun := fun x => ⟨ULift.up x.val, mem_planarSet_of_mem_pantsSlab x⟩
    invFun := fun y => ⟨y.val.down, mem_pantsSlab_of_mem_planarSet y⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    contMDiff_toFun := ((planarAtlas 3).contMDiff_iff_subtype_val _).mpr
      (contMDiff_planeLift_up.comp pantsSlabAtlas.contMDiff_subtype_val)
    contMDiff_invFun :=
      (pantsSlabAtlas.contMDiff_iff_subtype_val _).mpr (contMDiff_planarSet_down 3) }

theorem pantsSlabDiffeomorph_val (x : slabSet pantsHeight 0 1) :
    letI := pantsSlabAtlas.toChartedSpace
    (pantsSlabDiffeomorph.{w} x).val.down = x.val :=
  rfl

theorem exists_planarBase_of_saddleSlab (hU : OneSaddleSlabUniqueness.{uN, 0})
    {E H : Type} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ N]
    (hdim : Module.finrank ℝ E = 2) {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsConnected (f ⁻¹' Icc a b))
    (hlow : ¬ IsPreconnected (f ⁻¹' {a})) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    ∃ e : planarSet.{w} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f a b,
      ∀ j t, f (e (pantsPlanarBase.{w}.collar j (t, halfZero))) = if j.val = 0 then b else a := by
  let := (slabAtlas hdim hf hab hreg).toChartedSpace
  have hp0 : pantsHeight 0 ∈ Ioo (0 : ℝ) 1 := by
    rw [pantsHeight_zero]
    norm_num
  obtain ⟨e₁, he₁⟩ := hU E H N ℂ ℂ ℂ I 𝓘(ℝ, ℂ) hdim Complex.finrank_real_complex f pantsHeight
    hf contDiff_pantsHeight.contMDiff a b 0 1 hab zero_lt_one hreg pantsHeight_regular_endpoints
    p 0 hp hp0 hnd isNondegenerateCriticalPointAt_pantsHeight_zero hidx
    sigNeg_chartHessianAt_pantsHeight_zero huniq
    (fun z hz hc => (isCriticalPointAt_pantsHeight_iff hz).mp hc) hcpt
    isCompact_pantsHeight_preimage_Icc hconn isConnected_pantsHeight_preimage_Icc hlow
    not_isPreconnected_pantsHeight_zero
  let := pantsSlabAtlas.toChartedSpace
  refine ⟨(e₁.trans pantsSlabDiffeomorph.{w}).symm, fun j t => ?_⟩
  set y := (e₁.trans pantsSlabDiffeomorph.{w}).symm (pantsPlanarBase.{w}.collar j (t, halfZero))
  have hy : pantsSlabDiffeomorph.{w} (e₁ y) = pantsPlanarBase.{w}.collar j (t, halfZero) :=
    (e₁.trans pantsSlabDiffeomorph.{w}).apply_symm_apply _
  have hval : (e₁ y).val = planarCircleMap 3 j t := by
    rw [← pantsSlabDiffeomorph_val, hy]
    exact pantsPlanarBase.{w}.embedding_collar j t
  have hH := pantsHeight_planarCircleMap j t
  rw [← hval] at hH
  obtain ⟨hA, hB⟩ := he₁ y
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte] at hH ⊢
    exact hB.mpr hH
  · simp only [hj, ↓reduceIte] at hH ⊢
    exact hA.mpr hH

theorem sigPos_add_sigNeg_eq_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : QuadraticForm ℝ E)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    sigPos Q + sigNeg Q = Module.finrank ℝ E := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (𝕜 := ℝ) (Q := Q)
  have hrad : Q.radical = ⊥ := by
    rw [QuadraticMap.radical_eq_ker_associated, ← LinearMap.separatingLeft_iff_ker_eq_bot]
    exact hQ
  rw [hrad, finrank_bot, add_zero] at h
  exact h

theorem exists_planarBase_of_saddleSlab_upper (hU : OneSaddleSlabUniqueness.{uN, 0})
    {E H : Type} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ N]
    (hdim : Module.finrank ℝ E = 2) {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsConnected (f ⁻¹' Icc a b))
    (hup : ¬ IsPreconnected (f ⁻¹' {b})) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    ∃ e : planarSet.{w} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f a b,
      ∀ j t, f (e (pantsPlanarBase.{w}.collar j (t, halfZero))) = if j.val = 0 then a else b := by
  let C := slabAtlas hdim hf hab hreg
  let := C.toChartedSpace
  have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => -f x) := hf.neg
  have hab' : -b < -a := neg_lt_neg hab
  have hreg' : ∀ x, -f x = -b ∨ -f x = -a →
      mfderiv I 𝓘(ℝ, ℝ) (fun x => -f x) x ≠ 0 := by
    intro x hx h
    refine hreg x ?_ ((NegDual.isCriticalPointAt_neg_iff I f x).mp h)
    rcases hx with h' | h'
    · exact Or.inr (neg_inj.mp h')
    · exact Or.inl (neg_inj.mp h')
  have hp' : -f p ∈ Ioo (-b) (-a) := NegDual.neg_mem_Ioo_iff.mpr hp
  have hnd' := (NegDual.isNondegenerateCriticalPointAt_neg_iff I f p).mpr hnd
  have hidx' : sigNeg (chartHessianAt (fun y => -f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1 := by
    rw [NegDual.chartHessianAt_neg, sigNeg_neg]
    have h := sigPos_add_sigNeg_eq_finrank _ hnd.2
    omega
  have huniq' : ∀ x, -f x ∈ Icc (-b) (-a) →
      IsCriticalPointAt I (fun x => -f x) x → x = p := fun x hx hc =>
    huniq x (NegDual.neg_mem_Icc_iff.mp hx) ((NegDual.isCriticalPointAt_neg_iff I f x).mp hc)
  have hcpt' : IsCompact ((fun x => -f x) ⁻¹' Icc (-b) (-a)) := by
    rw [NegDual.preimage_neg_Icc]
    exact hcpt
  have hconn' : IsConnected ((fun x => -f x) ⁻¹' Icc (-b) (-a)) := by
    rw [NegDual.preimage_neg_Icc]
    exact hconn
  have hlow' : ¬ IsPreconnected ((fun x => -f x) ⁻¹' {-b}) := by
    rw [NegDual.preimage_neg_singleton]
    exact hup
  obtain ⟨e₁, he₁⟩ := exists_planarBase_of_saddleSlab.{w} hU I hdim hg hab' hreg' hp' hnd'
    hidx' huniq' hcpt' hconn' hlow'
  let C' := slabAtlas hdim hg hab' hreg'
  let := C'.toChartedSpace
  have hto : ∀ x : slabSet (fun x => -f x) (-b) (-a), x.val ∈ slabSet f a b := fun x =>
    (mem_slabSet_iff hab.le _).mpr (NegDual.neg_mem_Icc_iff.mp
      ((mem_slabSet_iff hab'.le _).mp x.2))
  have hinv : ∀ y : slabSet f a b, y.val ∈ slabSet (fun x => -f x) (-b) (-a) := fun y =>
    (mem_slabSet_iff hab'.le _).mpr (NegDual.neg_mem_Icc_iff.mpr
      ((mem_slabSet_iff hab.le _).mp y.2))
  let e₂ : slabSet (fun x => -f x) (-b) (-a) ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f a b :=
    { toFun := fun x => ⟨x.val, hto x⟩
      invFun := fun y => ⟨y.val, hinv y⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun := (C.contMDiff_iff_subtype_val _).mpr C'.contMDiff_subtype_val
      contMDiff_invFun := (C'.contMDiff_iff_subtype_val _).mpr C.contMDiff_subtype_val }
  refine ⟨e₁.trans e₂, fun j t => ?_⟩
  have h := he₁ j t
  change f (e₁ (pantsPlanarBase.{w}.collar j (t, halfZero))).val = _
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte] at h ⊢
    linarith
  · simp only [hj, ↓reduceIte] at h ⊢
    linarith

theorem exists_saddleChart_two {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel 2) H) [I.Boundaryless]
    [IsManifold I ∞ M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ Φ : OpenPartialHomeomorph (MorseModel 2) M, Φ 0 = p ∧
      (∀ y : MorseModel 2, morseNorm 2 y ≤ R →
        y ∈ Φ.source ∧ f (Φ y) = f p + (y 1 ^ 2 - y 0 ^ 2) / 2) ∧
      ∃ R' : ℝ, 0 < R' ∧ ContMDiffOn 𝓘(ℝ, MorseModel 2) I ∞ Φ (ball 0 R') ∧
        ContMDiffOn I 𝓘(ℝ, MorseModel 2) ∞ Φ.symm (Φ '' ball 0 R') := by
  obtain ⟨R, hR, Φ, -, -, hΦ0, hsrc, hform, -, -, R', hR', hon, hsymm⟩ :=
    morse_lemma I f hf p 1 (by norm_num) hnd hindex
  refine ⟨R, hR, Φ, hΦ0, fun y hy => ⟨hsrc y hy, ?_⟩, R', hR', hon, hsymm⟩
  rw [hform y hy]
  simp [morseNormalForm, negIdx, posIdx]
  ring

end GC.Seifert
