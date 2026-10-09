import DifferentialGeometry.Topology.PlanarJordan.CutBoundaryExtension
import DifferentialGeometry.Topology.PlanarJordan.Crosscut
import DifferentialGeometry.Topology.PiecewiseLinear.JordanDiskPasting
import DifferentialGeometry.Topology.PlanarJordan.PlanarTubeSmoothing
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningJunction
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Homeomorph.PlanarExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension
import DifferentialGeometry.Topology.Manifold.CompactPlanarIsotopy
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Straightening an arc in the square

Chapter 6, packet K08, lane MC3 of the `TorusMappingClassLinear` programme
(`docs/geometrization/handoffs/20261004-survey-torus-mapping-class.md`, corrected by review 12).

`exists_isotopy_square_arc`: a smooth regular arc `γ` of the unit square from `1/2` to `1/2 + i`,
injective on `[0, 1]`, inside the open square for `0 < t < 1`, and equal to the parametrised segment
`t ↦ 1/2 + t i` for `t ≤ δ` and `t ≥ 1 - δ`, is `H 1 ∘ (segment)` for an isotopy `H` of `ℂ` with
`H 0 = id`, jointly smooth with its inverse, fixing everything outside one compact subset of the
open square: `H 1 (1/2 + t i) = γ t` on the common parametrisation. Straightening uses `(H 1)⁻¹`.

Route.
* `squareChart`: the open square onto `ℂ`, `z ↦ tan (π (Re z - 1/2)) + tan (π (Im z - 1/2)) i`,
  smooth both ways. In this chart, and after the linear identification `planeOfComplex` of `ℂ`
  with `Plane` sending `s i` to `(s, 0)`, the arc becomes a regular injective line `Γ` equal to
  the axis `s ↦ (s, 0)` for `|s| ≥ s₀` (regularity is kept by the chain rule).
* S-MC3, `exists_axis_germ`: the tube map `tubeMap Γ (x₀, x₁) = Γ x₀ + x₁ • perp (Γ' x₀)` has
  determinant `‖Γ'‖² > 0` along the axis (regularity of `Γ` is used here), hence is a local
  diffeomorphism there; it is injective on the compact axis segment, hence on a neighbourhood
  (`exists_isOpen_injOn_of_isCompact`); it is the identity for `|x₀| > s₀`. Glued with the
  identity near the circle of radius `R`, it is one partial diffeomorphism `c` with
  `c (s, 0) = Γ s`: the common tubular germ along the shared arc, the identity germ near the outer
  boundary.
* The two half discs `halfDisc R (±1)`, bounded by a semicircle and the axis segment, have
  right-angle corners at `(±R, 0)`; `bandChart R` straightens them into the band model, and the
  band corner Schoenflies theorem (`PlanarJordan.CutBoundaryExtension`) gives `F±` equal to `c`
  near each half disc boundary and mapping it onto the closed inside of
  `semicircle ∪ Γ [-R, R]`. The hypothesis that `c` respects the closed insides is
  `exists_closure_inside_iff_of_outside`: both sides of a collar `e⁻¹ (annulus)` of the first
  curve (topological Schoenflies) are connected, a point just outside the circle is fixed by `c`
  and outside both curves, and the second curve lies in the frontier of its inside.
* `exists_diffeomorph_axis_line`: `Q = F₊` on the upper half disc, `F₋` on the lower one, the
  identity outside the disc; the general crosscut theorem for `Γ [-R, R]` in the disc shows that
  the two target regions tile the disc and meet along `Γ [-R, R]`, and `Q` is locally one of
  `F±`, `c`, `id` (its inverse locally `F±⁻¹`, `c⁻¹`, `id`), so it is a diffeomorphism of `Plane`
  fixing everything outside the disc, with `Q (s, 0) = Γ s`.
* Back in the square: the compactly supported planar isotopy of the conjugate of `Q`
  (`exists_compactly_supported_planar_isotopy`) is transported through `squareChart`
  (`exists_diffeomorph_extension_of_chart_family`) and reversed in time.
-/

set_option autoImplicit false

noncomputable section
open Set Metric
open scoped Manifold ContDiff Topology

namespace GC.Seifert

def openSquare : Set ℂ := Complex.reProdIm (Ioo 0 1) (Ioo 0 1)

open Schoenflies (Plane IsJordanCurve inside outside)

private theorem mem_outside_of_lt_norm {J : Set Plane} {R : ℝ} (hR : 0 ≤ R)
    (hJ : J ⊆ closedBall 0 R)
    {x : Plane} (hx : R < ‖x‖) : x ∈ outside J := by
  let ray : Set Plane := (fun t : ℝ => t • x) '' Ici 1
  have hnorm (t : ℝ) (ht : t ∈ Ici (1 : ℝ)) : ‖x‖ ≤ ‖t • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]
    exact le_mul_of_one_le_left (norm_nonneg x) ht
  have hconn : IsPreconnected ray :=
    isPreconnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
  have hsub : ray ⊆ Jᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hJt
    have h1 := mem_closedBall_zero_iff.mp (hJ hJt)
    linarith [hnorm t ht]
  have hxray : x ∈ ray := ⟨1, mem_Ici.mpr le_rfl, one_smul ℝ x⟩
  refine ⟨hsub hxray, fun hb => ?_⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (hb.subset (hconn.subset_connectedComponentIn hxray hsub))
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
  set t : ℝ := (|C| + 1) / ‖x‖ + 1 with htdef
  have ht : t ∈ Ici (1 : ℝ) := by
    rw [mem_Ici, htdef]
    have : 0 ≤ (|C| + 1) / ‖x‖ := by positivity
    linarith
  have h1 := hC (t • x) ⟨t, ht, rfl⟩
  rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht), htdef, add_mul,
    div_mul_cancel₀ _ hxpos.ne'] at h1
  linarith [le_abs_self C, norm_nonneg x]

private theorem isPreconnected_annulus {a b : ℝ} (ha : 0 < a) :
    IsPreconnected {y : Plane | a < ‖y‖ ∧ ‖y‖ < b} := by
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hS : IsPreconnected (sphere (0 : Plane) 1) :=
    (isConnected_sphere hrank 0 zero_le_one).isPreconnected
  have heq : {y : Plane | a < ‖y‖ ∧ ‖y‖ < b} =
      (fun p : Plane × ℝ => p.2 • p.1) '' (sphere 0 1 ×ˢ Ioo a b) := by
    ext y
    constructor
    · rintro ⟨hya, hyb⟩
      have hy0 : ‖y‖ ≠ 0 := (ha.trans hya).ne'
      refine ⟨(‖y‖⁻¹ • y, ‖y‖), ⟨?_, hya, hyb⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy0]
      · simp only [smul_smul, mul_inv_cancel₀ hy0, one_smul]
    · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, rfl⟩
      have hv1 : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
      simp only [mem_ofPred_eq, norm_smul, hv1, mul_one, Real.norm_of_nonneg (ha.trans hr.1).le]
      exact hr
  rw [heq]
  exact (hS.prod isPreconnected_Ioo).image _
    (continuous_snd.smul continuous_fst).continuousOn

open DifferentialGeometry.Topology.PiecewiseLinear in
theorem exists_closure_inside_iff_of_outside {J₀ J₁ : Set Plane} (hJ₀ : IsJordanCurve J₀)
    (hJ₁ : IsJordanCurve J₁) (c : OpenPartialHomeomorph Plane Plane) (hs : J₀ ⊆ c.source)
    (himg : c '' J₀ = J₁)
    (hout : ∀ W : Set Plane, IsOpen W → J₀ ⊆ W →
      ∃ x ∈ W, x ∈ c.source ∧ x ∈ outside J₀ ∧ c x ∈ outside J₁) :
    ∃ V : Set Plane, IsOpen V ∧ J₀ ⊆ V ∧ V ⊆ c.source ∧
      ∀ x ∈ V, (c x ∈ closure (inside J₁) ↔ x ∈ closure (inside J₀)) := by
  obtain ⟨e, heJ, heC, heI⟩ :=
    exists_homeomorph_image_closure_inside_eq_closedBall hJ₀
  have hsep₀ := Schoenflies.jordan_curve_theorem hJ₀
  have hsep₁ := Schoenflies.jordan_curve_theorem hJ₁
  have hcl₀ := (Schoenflies.IsRegionOf.inside J₀).closure_eq hsep₀
  have hcl₁ := (Schoenflies.IsRegionOf.inside J₁).closure_eq hsep₁
  have hmemJ (x : Plane) : x ∈ J₀ ↔ e x ∈ sphere (0 : Plane) 1 := by
    rw [← heJ]
    exact e.injective.mem_set_image.symm
  have hmemI (x : Plane) : x ∈ inside J₀ ↔ e x ∈ ball (0 : Plane) 1 := by
    rw [← heI]
    exact e.injective.mem_set_image.symm
  have hmemC (x : Plane) : x ∈ closure (inside J₀) ↔ e x ∈ closedBall (0 : Plane) 1 := by
    rw [← heC]
    exact e.injective.mem_set_image.symm
  have hSopen : IsOpen (e '' c.source) := e.isOpenMap _ c.open_source
  have hSsub : sphere (0 : Plane) 1 ⊆ e '' c.source := by
    rw [← heJ]
    exact image_mono hs
  obtain ⟨ρ, hρ, hρsub⟩ := Schoenflies.Plane.exists_thickening_subset (isCompact_sphere 0 1)
    hSopen hSsub
  set δ : ℝ := min ρ (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min hρ (by norm_num)
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδh : δ ≤ 1 / 2 := min_le_right _ _
  have hann : ∀ y : Plane, 1 - δ < ‖y‖ → ‖y‖ < 1 + δ → y ∈ e '' c.source := by
    intro y h1 h2
    apply hρsub
    have hy0 : ‖y‖ ≠ 0 := by linarith
    rw [mem_thickening_iff]
    refine ⟨‖y‖⁻¹ • y, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy0]
    · rw [dist_eq_norm]
      have : y - ‖y‖⁻¹ • y = (1 - ‖y‖⁻¹) • y := by rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs]
      have hpos : 0 < ‖y‖ := by linarith
      calc |1 - ‖y‖⁻¹| * ‖y‖ = |(1 - ‖y‖⁻¹) * ‖y‖| := by
            rw [abs_mul, abs_of_pos hpos]
        _ = |‖y‖ - 1| := by rw [show (1 - ‖y‖⁻¹) * ‖y‖ = ‖y‖ - 1 by field_simp]
        _ < ρ := by
            rw [abs_lt]
            constructor <;> linarith
  let V : Set Plane := e ⁻¹' {y | 1 - δ < ‖y‖ ∧ ‖y‖ < 1 + δ}
  let Vin : Set Plane := e ⁻¹' {y | 1 - δ < ‖y‖ ∧ ‖y‖ < 1}
  let Vout : Set Plane := e ⁻¹' {y | 1 < ‖y‖ ∧ ‖y‖ < 1 + δ}
  have hVopen : IsOpen V := by
    apply IsOpen.preimage e.continuous
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hJV : J₀ ⊆ V := by
    intro x hx
    have h1 : ‖e x‖ = 1 := mem_sphere_zero_iff_norm.mp ((hmemJ x).mp hx)
    change 1 - δ < ‖e x‖ ∧ ‖e x‖ < 1 + δ
    rw [h1]
    constructor <;> linarith
  have hVs : V ⊆ c.source := by
    intro x hx
    obtain ⟨x', hx', hxe⟩ := hann (e x) hx.1 hx.2
    rw [← e.injective hxe]
    exact hx'
  have hsplit : ∀ x ∈ V, x ∈ Vin ∨ x ∈ J₀ ∨ x ∈ Vout := by
    intro x hx
    rcases lt_trichotomy ‖e x‖ 1 with h | h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr (Or.inl ((hmemJ x).mpr (mem_sphere_zero_iff_norm.mpr h)))
    · exact Or.inr (Or.inr ⟨h, hx.2⟩)
  have hVin : Vin ⊆ inside J₀ := fun x hx =>
    (hmemI x).mpr (mem_ball_zero_iff.mpr hx.2)
  have hVout : Vout ⊆ outside J₀ := by
    intro x hx
    have hnc : x ∉ closure (inside J₀) := by
      rw [hmemC x, mem_closedBall_zero_iff]
      exact not_le.mpr hx.1
    rw [hcl₀] at hnc
    have hxc : x ∈ J₀ᶜ := fun h => hnc (Or.inr h)
    rw [← Schoenflies.inside_union_outside J₀] at hxc
    exact hxc.resolve_left fun h => hnc (Or.inl h)
  have hVinV : Vin ⊆ V := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hVoutV : Vout ⊆ V := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hpre (a b : ℝ) (ha : 0 < a) : IsPreconnected (e ⁻¹' {y : Plane | a < ‖y‖ ∧ ‖y‖ < b}) := by
    rw [← e.image_symm]
    exact (isPreconnected_annulus ha).image _ e.symm.continuous.continuousOn
  have hVinc : IsPreconnected Vin := hpre _ _ (by linarith)
  have hVoutc : IsPreconnected Vout := hpre _ _ one_pos
  have hdisj : ∀ x ∈ V, x ∉ J₀ → c x ∉ J₁ := by
    intro x hx hxJ hcx
    rw [← himg] at hcx
    obtain ⟨x', hx', hxx'⟩ := hcx
    exact hxJ (c.injOn (hs hx') (hVs hx) hxx' ▸ hx')
  have hJin : Disjoint (inside J₀) J₀ := disjoint_left.mpr fun _ h => h.1
  have hJout : Disjoint (outside J₀) J₀ := disjoint_left.mpr fun _ h => h.1
  have hcVoutc : IsPreconnected (c '' Vout) :=
    hVoutc.image _ (c.continuousOn.mono (hVoutV.trans hVs))
  have hcVinc : IsPreconnected (c '' Vin) :=
    hVinc.image _ (c.continuousOn.mono (hVinV.trans hVs))
  have hcVoutJ : c '' Vout ⊆ J₁ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdisj x (hVoutV hx) (disjoint_left.mp hJout (hVout hx))
  have hcVinJ : c '' Vin ⊆ J₁ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdisj x (hVinV hx) (disjoint_left.mp hJin (hVin hx))
  obtain ⟨x₀, hx₀V, -, hx₀out, hcx₀⟩ := hout V hVopen hJV
  have hx₀ : x₀ ∈ Vout := by
    rcases hsplit x₀ hx₀V with h | h | h
    · exact absurd (hVin h) (disjoint_left.mp Schoenflies.disjoint_inside_outside.symm hx₀out)
    · exact absurd h hx₀out.1
    · exact h
  have hcVout : c '' Vout ⊆ outside J₁ :=
    (hcVoutc.subset_connectedComponentIn ⟨x₀, hx₀, rfl⟩ hcVoutJ).trans
      (Schoenflies.connectedComponentIn_subset_outside hcx₀)
  have hcVopen : IsOpen (c '' V) := c.isOpen_image_of_subset_source hVopen hVs
  obtain ⟨y₀, hy₀⟩ := hsep₁.isConnected_inside.nonempty
  have hJ₁ne : J₁.Nonempty := by
    obtain ⟨f, hf, hfI⟩ := hJ₁
    exact ⟨f 0, hfI ▸ mem_image_of_mem f Schoenflies.zero_mem_I⟩
  obtain ⟨z₁, hz₁⟩ := hJ₁ne
  have hz₁cl : z₁ ∈ closure (inside J₁) := by
    rw [← hsep₁.frontier_inside] at hz₁
    exact frontier_subset_closure hz₁
  have hz₁V : z₁ ∈ c '' V := by
    rw [← himg] at hz₁
    exact image_mono hJV hz₁
  obtain ⟨_, ⟨x₁, hx₁V, rfl⟩, hcx₁⟩ :=
    mem_closure_iff.mp hz₁cl (c '' V) hcVopen hz₁V
  have hx₁ : x₁ ∈ Vin := by
    rcases hsplit x₁ hx₁V with h | h | h
    · exact h
    · exact absurd (himg ▸ mem_image_of_mem c h) hcx₁.1
    · exact absurd (hcVout ⟨x₁, h, rfl⟩)
        (disjoint_left.mp Schoenflies.disjoint_inside_outside hcx₁)
  have hcVin : c '' Vin ⊆ inside J₁ :=
    (hcVinc.subset_connectedComponentIn ⟨x₁, hx₁, rfl⟩ hcVinJ).trans
      (Schoenflies.connectedComponentIn_subset_inside hcx₁)
  refine ⟨V, hVopen, hJV, hVs, fun x hx => ?_⟩
  rw [hcl₀, hcl₁]
  rcases hsplit x hx with h | h | h
  · exact ⟨fun _ => Or.inl (hVin h), fun _ => Or.inl (hcVin ⟨x, h, rfl⟩)⟩
  · exact ⟨fun _ => Or.inr h, fun _ => Or.inr (himg ▸ mem_image_of_mem c h)⟩
  · constructor
    · rintro (h' | h')
      · exact absurd h' (disjoint_left.mp Schoenflies.disjoint_inside_outside.symm
          (hcVout ⟨x, h, rfl⟩))
      · exact absurd h' (hcVoutJ ⟨x, h, rfl⟩)
    · rintro (h' | h')
      · exact absurd h' (disjoint_left.mp Schoenflies.disjoint_inside_outside.symm (hVout h))
      · exact absurd h' (hVout h).1


private theorem planeNormSq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem continuous_planeCoord (i : Fin 2) : Continuous (fun x : Plane => x i) :=
  (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).continuous

private theorem continuous_planeMk :
    Continuous (fun p : ℝ × ℝ => Schoenflies.Plane.mk p.1 p.2) := by
  simp only [DifferentialGeometry.Topology.PlanarJordan.planeMk_eq_smul_add]
  fun_prop

private theorem planeExt {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

private def halfDisc (R b : ℝ) : Set Plane := {x | ‖x‖ ≤ R ∧ 0 ≤ b * x 1}

private def semicircle (R b : ℝ) : Set Plane := {x | ‖x‖ = R ∧ 0 ≤ b * x 1}

def axisSegment (R : ℝ) : Set Plane := {x | x 1 = 0 ∧ |x 0| ≤ R}

private theorem sq_eq_one_cases {b : ℝ} (hb : b ^ 2 = 1) : b = 1 ∨ b = -1 := by
  have : (b - 1) * (b + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

private theorem interior_halfDisc {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    interior (halfDisc R b) = {x | ‖x‖ < R ∧ 0 < b * x 1} := by
  let g : Plane →L[ℝ] ℝ := b • EuclideanSpace.proj (1 : Fin 2)
  have hb0 : b ≠ 0 := by rintro rfl; norm_num at hb
  have hg : g ≠ 0 := by
    intro h
    have := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 1 1)) h
    simp [g, hb0] at this
  have hhalf : {x : Plane | 0 ≤ b * x 1} = g ⁻¹' Ici 0 := by
    ext x
    simp [g]
  have hint : interior {x : Plane | 0 ≤ b * x 1} = {x : Plane | 0 < b * x 1} := by
    rw [hhalf, ← (g.isOpenMap_of_ne_zero hg).preimage_interior_eq_interior_preimage g.continuous,
      interior_Ici]
    ext x
    simp [g]
  have hset : halfDisc R b = closedBall 0 R ∩ {x : Plane | 0 ≤ b * x 1} := by
    ext x
    simp [halfDisc]
  rw [hset, interior_inter, interior_closedBall _ hR.ne', hint]
  ext x
  simp

private theorem frontier_halfDisc {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    frontier (halfDisc R b) = semicircle R b ∪ axisSegment R := by
  have hclosed : IsClosed (halfDisc R b) :=
    (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_const.mul (continuous_planeCoord 1)))
  rw [frontier, hclosed.closure_eq, interior_halfDisc hR hb]
  have hb0 : b ≠ 0 := by rintro rfl; norm_num at hb
  ext x
  simp only [halfDisc, semicircle, axisSegment, mem_sdiff, mem_ofPred_eq, mem_union, not_and_or,
    not_lt]
  have hn := planeNormSq x
  constructor
  · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
    · exact Or.inl ⟨le_antisymm h1 h3, h2⟩
    · right
      have hx1 : b * x 1 = 0 := le_antisymm h3 h2
      have hx1' : x 1 = 0 := by
        rcases mul_eq_zero.mp hx1 with h | h
        · exact absurd h hb0
        · exact h
      refine ⟨hx1', ?_⟩
      rw [hx1'] at hn
      have : |x 0| = ‖x‖ := by
        rw [← Real.sqrt_sq (abs_nonneg (x 0)), sq_abs, ← Real.sqrt_sq (norm_nonneg x), hn]
        ring_nf
      linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨h1.le, h2⟩, Or.inl h1.ge⟩
    · rw [h1] at hn ⊢
      have : ‖x‖ = |x 0| := by
        rw [← Real.sqrt_sq (abs_nonneg (x 0)), sq_abs, ← Real.sqrt_sq (norm_nonneg x), hn]
        ring_nf
      exact ⟨⟨by linarith, by simp⟩, Or.inr (by simp)⟩

private def semicircleParam (R b t : ℝ) : Plane :=
  Schoenflies.Plane.mk (-R * Real.cos (Real.pi * t)) (b * R * Real.sin (Real.pi * t))

private theorem isArcBetween_semicircle {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    Schoenflies.IsArcBetween (semicircle R b) (Schoenflies.Plane.mk (-R) 0)
      (Schoenflies.Plane.mk R 0) := by
  refine ⟨semicircleParam R b, ?_, ?_, ?_, ?_, ?_⟩
  · apply Continuous.continuousOn
    have h1 : Continuous (fun t : ℝ => (-R * Real.cos (Real.pi * t),
        b * R * Real.sin (Real.pi * t))) := by fun_prop
    exact continuous_planeMk.comp h1
  · intro s hs t ht hst
    have h0 := congrArg (fun x : Plane => x 0) hst
    simp only [semicircleParam, Schoenflies.Plane.mk_zero] at h0
    have hc : Real.cos (Real.pi * s) = Real.cos (Real.pi * t) := by
      have := mul_left_cancel₀ (neg_ne_zero.mpr hR.ne') h0
      exact this
    have hs' : Real.pi * s ∈ Icc 0 Real.pi :=
      ⟨mul_nonneg Real.pi_pos.le hs.1, by nlinarith [Real.pi_pos, hs.2]⟩
    have ht' : Real.pi * t ∈ Icc 0 Real.pi :=
      ⟨mul_nonneg Real.pi_pos.le ht.1, by nlinarith [Real.pi_pos, ht.2]⟩
    exact mul_left_cancel₀ Real.pi_pos.ne' (Real.injOn_cos hs' ht' hc)
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hsin : 0 ≤ Real.sin (Real.pi * t) := Real.sin_nonneg_of_nonneg_of_le_pi
        (mul_nonneg Real.pi_pos.le ht.1) (by nlinarith [Real.pi_pos, ht.2])
      refine ⟨?_, ?_⟩
      · have : ‖semicircleParam R b t‖ ^ 2 = R ^ 2 := by
          rw [planeNormSq]
          simp only [semicircleParam, Schoenflies.Plane.mk_zero, Schoenflies.Plane.mk_one]
          have := Real.sin_sq_add_cos_sq (Real.pi * t)
          calc (-R * Real.cos (Real.pi * t)) ^ 2 + (b * R * Real.sin (Real.pi * t)) ^ 2
              = R ^ 2 * (b ^ 2 * Real.sin (Real.pi * t) ^ 2 + Real.cos (Real.pi * t) ^ 2) := by
                ring
            _ = R ^ 2 := by rw [hb, one_mul, this, mul_one]
        exact (pow_left_inj₀ (norm_nonneg _) hR.le two_ne_zero).mp this
      · simp only [semicircleParam, Schoenflies.Plane.mk_one]
        have : b * (b * R * Real.sin (Real.pi * t)) = b ^ 2 * R * Real.sin (Real.pi * t) := by
          ring
        rw [this, hb, one_mul]
        exact mul_nonneg hR.le hsin
    · rintro ⟨h1, h2⟩
      have hn := planeNormSq x
      rw [h1] at hn
      have hx0 : |x 0| ≤ R := by
        have : x 0 ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg (x 1)]
        exact (sq_le_sq₀ (abs_nonneg _) hR.le).mp (by rw [sq_abs]; exact this)
      have hle := abs_le.mp hx0
      have ha1 : -1 ≤ -x 0 / R := by
        rw [le_div_iff₀ hR]; linarith
      have ha2 : -x 0 / R ≤ 1 := by
        rw [div_le_iff₀ hR]; linarith
      have hx1abs : b * |x 1| = x 1 := by
        rcases sq_eq_one_cases hb with rfl | rfl
        · rw [one_mul, abs_of_nonneg (by linarith)]
        · rw [abs_of_nonpos (by linarith)]; ring
      refine ⟨Real.arccos (-x 0 / R) / Real.pi, ⟨by
          exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le, by
          rw [div_le_one Real.pi_pos]; exact Real.arccos_le_pi _⟩, ?_⟩
      have hpi : Real.pi * (Real.arccos (-x 0 / R) / Real.pi) = Real.arccos (-x 0 / R) := by
        field_simp
      have hsq : Real.sqrt (1 - (-x 0 / R) ^ 2) = |x 1| / R := by
        rw [show 1 - (-x 0 / R) ^ 2 = (|x 1| / R) ^ 2 by
          field_simp; rw [sq_abs]; linarith]
        exact Real.sqrt_sq (div_nonneg (abs_nonneg _) hR.le)
      apply planeExt
      · change -R * Real.cos (Real.pi * _) = x 0
        rw [hpi, Real.cos_arccos ha1 ha2]
        field_simp
      · change b * R * Real.sin (Real.pi * _) = x 1
        rw [hpi, Real.sin_arccos, hsq]
        have : b * R * (|x 1| / R) = b * |x 1| := by field_simp
        rw [this, hx1abs]
  · simp [semicircleParam]
  · simp [semicircleParam]


private theorem isArcBetween_axisSegment {R : ℝ} (hR : 0 < R) :
    Schoenflies.IsArcBetween (axisSegment R) (Schoenflies.Plane.mk (-R) 0)
      (Schoenflies.Plane.mk R 0) := by
  refine ⟨fun t => Schoenflies.Plane.mk (-R + 2 * R * t) 0, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_planeMk.comp ((continuous_const.add (continuous_const.mul
      continuous_id)).prodMk continuous_const)).continuousOn
  · intro s _ t _ hst
    have h0 : -R + 2 * R * s = -R + 2 * R * t := congrArg (fun x : Plane => x 0) hst
    have : 2 * R * s = 2 * R * t := by linarith
    exact mul_left_cancel₀ (by positivity) this
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨rfl, ?_⟩
      change |-R + 2 * R * t| ≤ R
      rw [abs_le]
      constructor <;> nlinarith [ht.1, ht.2]
    · rintro ⟨h1, h2⟩
      refine ⟨(x 0 + R) / (2 * R), ⟨?_, ?_⟩, ?_⟩
      · have := (abs_le.mp h2).1
        exact div_nonneg (by linarith) (by positivity)
      · rw [div_le_one (by positivity)]
        linarith [(abs_le.mp h2).2]
      · apply planeExt
        · change -R + 2 * R * ((x 0 + R) / (2 * R)) = x 0
          field_simp
          ring
        · exact h1.symm
  · simp
  · apply planeExt
    · simp; ring
    · simp

private theorem semicircle_inter_axisSegment {R b : ℝ} :
    ∀ z ∈ semicircle R b, z ∈ axisSegment R →
      z = Schoenflies.Plane.mk (-R) 0 ∨ z = Schoenflies.Plane.mk R 0 := by
  rintro z ⟨h1, -⟩ ⟨h2, -⟩
  have hn := planeNormSq z
  rw [h1, h2] at hn
  have : (z 0 + R) * (z 0 - R) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · left; apply planeExt <;> simp <;> linarith
  · right; apply planeExt <;> simp <;> linarith

private theorem isJordanCurve_halfDiscCurve {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    IsJordanCurve (semicircle R b ∪ axisSegment R) :=
  Schoenflies.isJordanCurve_union (isArcBetween_semicircle hR hb) (isArcBetween_axisSegment hR)
    semicircle_inter_axisSegment

private theorem isCompact_halfDisc (R b : ℝ) : IsCompact (halfDisc R b) := by
  apply (isCompact_closedBall (0 : Plane) R).of_isClosed_subset
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_const.mul (continuous_planeCoord 1)))
  · intro x hx
    exact mem_closedBall_zero_iff.mpr hx.1

private theorem interior_halfDisc_nonempty {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    (interior (halfDisc R b)).Nonempty := by
  rw [interior_halfDisc hR hb]
  refine ⟨Schoenflies.Plane.mk 0 (b * (R / 2)), ?_, ?_⟩
  · have : ‖Schoenflies.Plane.mk 0 (b * (R / 2))‖ ^ 2 = (R / 2) ^ 2 := by
      rw [planeNormSq]
      change (0 : ℝ) ^ 2 + (b * (R / 2)) ^ 2 = (R / 2) ^ 2
      rw [mul_pow, hb]
      ring
    have h2 := (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
    rw [h2]
    linarith
  · change 0 < b * (b * (R / 2))
    have : b * (b * (R / 2)) = b ^ 2 * (R / 2) := by ring
    rw [this, hb]
    linarith

private theorem closure_inside_halfDiscCurve {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    closure (inside (semicircle R b ∪ axisSegment R)) = halfDisc R b := by
  have h := DifferentialGeometry.Topology.PlanarJordan.closure_inside_frontier_eq_of_isCompact
    (isCompact_halfDisc R b)
    (by rw [frontier_halfDisc hR hb]; exact isJordanCurve_halfDiscCurve hR hb)
    (interior_halfDisc_nonempty hR hb)
  rwa [frontier_halfDisc hR hb] at h

private theorem inside_halfDiscCurve {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    inside (semicircle R b ∪ axisSegment R) = {x | ‖x‖ < R ∧ 0 < b * x 1} := by
  have h := DifferentialGeometry.Topology.PlanarJordan.interior_eq_inside_frontier_of_isCompact
    (isCompact_halfDisc R b)
    (by rw [frontier_halfDisc hR hb]; exact isJordanCurve_halfDiscCurve hR hb)
    (interior_halfDisc_nonempty hR hb)
  rw [frontier_halfDisc hR hb, interior_halfDisc hR hb] at h
  exact h.symm

private theorem isJordanCurve_sphere' {R : ℝ} (hR : 0 < R) :
    IsJordanCurve (sphere (0 : Plane) R) := by
  have h : semicircle R 1 ∪ semicircle R (-1) = sphere (0 : Plane) R := by
    ext x
    simp only [semicircle, mem_union, mem_ofPred_eq, mem_sphere_zero_iff_norm, one_mul,
      neg_one_mul, neg_nonneg]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases le_total 0 (x 1) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  rw [← h]
  refine Schoenflies.isJordanCurve_union (isArcBetween_semicircle hR (by norm_num))
    (isArcBetween_semicircle hR (by norm_num)) ?_
  rintro z ⟨h1, h2⟩ ⟨-, h3⟩
  have hz1 : z 1 = 0 := by linarith
  exact semicircle_inter_axisSegment z ⟨h1, h2⟩
    ⟨hz1, by
      have hn := planeNormSq z
      rw [h1, hz1] at hn
      have : z 0 ^ 2 ≤ R ^ 2 := by linarith
      exact (sq_le_sq₀ (abs_nonneg _) hR.le).mp (by rw [sq_abs]; exact this)⟩

private theorem inside_sphere {R : ℝ} (hR : 0 < R) : inside (sphere (0 : Plane) R) = ball 0 R := by
  have h := DifferentialGeometry.Topology.PlanarJordan.interior_eq_inside_frontier_of_isCompact
    (isCompact_closedBall (0 : Plane) R)
    (by rw [frontier_closedBall _ hR.ne']; exact isJordanCurve_sphere' hR)
    (by rw [interior_closedBall _ hR.ne']; exact nonempty_ball.mpr hR)
  rw [frontier_closedBall _ hR.ne', interior_closedBall _ hR.ne'] at h
  exact h.symm

private theorem isCutPair_semicircles {R : ℝ} (hR : 0 < R) :
    Schoenflies.IsCutPair (sphere (0 : Plane) R) (Schoenflies.Plane.mk (-R) 0)
      (Schoenflies.Plane.mk R 0) (semicircle R 1) (semicircle R (-1)) where
  fst := isArcBetween_semicircle hR (by norm_num)
  snd := isArcBetween_semicircle hR (by norm_num)
  union_eq := by
    ext x
    simp only [semicircle, mem_union, mem_ofPred_eq, mem_sphere_zero_iff_norm, one_mul,
      neg_one_mul, neg_nonneg]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases le_total 0 (x 1) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  inter_eq := by
    ext z
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨-, h3⟩⟩
      have hz1 : z 1 = 0 := by linarith
      have hn := planeNormSq z
      rw [h1, hz1] at hn
      have : (z 0 + R) * (z 0 - R) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · left; apply planeExt <;> simp <;> linarith
      · right; apply planeExt <;> simp <;> linarith
    · rintro (rfl | rfl)
      · refine ⟨⟨?_, by simp⟩, ⟨?_, by simp⟩⟩ <;>
        · rw [← sq_eq_sq₀ (norm_nonneg _) hR.le, planeNormSq]; simp
      · refine ⟨⟨?_, by simp⟩, ⟨?_, by simp⟩⟩ <;>
        · rw [← sq_eq_sq₀ (norm_nonneg _) hR.le, planeNormSq]; simp


private def diffeoOfContDiff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (g : F → E) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : E ≃ₘ[ℝ] F where
  toFun := f
  invFun := g
  left_inv := hgf
  right_inv := hfg
  contMDiff_toFun := hf.contMDiff
  contMDiff_invFun := hg.contMDiff

private def bandSq (z : ℝ) : ℝ := z ^ 2 - (z ^ 2 - 1) * Real.smoothTransition (z ^ 2 - 1)

private theorem bandSq_eq {z : ℝ} (hz : z ^ 2 ≤ 1) : bandSq z = z ^ 2 := by
  rw [bandSq, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero, sub_zero]

private theorem bandSq_le (z : ℝ) : bandSq z ≤ 2 := by
  unfold bandSq
  have h0 := Real.smoothTransition.nonneg (z ^ 2 - 1)
  have h1 := Real.smoothTransition.le_one (z ^ 2 - 1)
  rcases le_total (z ^ 2) 1 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    linarith
  · rcases le_total (z ^ 2) 2 with h' | h'
    · nlinarith
    · rw [Real.smoothTransition.one_of_one_le (by linarith)]
      linarith

private theorem contDiff_bandSq : ContDiff ℝ ∞ bandSq := by
  unfold bandSq
  have h : ContDiff ℝ ∞ (fun z : ℝ => z ^ 2) := contDiff_id.pow 2
  exact h.sub ((h.sub contDiff_const).mul (Real.smoothTransition.contDiff.comp
    (h.sub contDiff_const)))

private def bandWidth (R z : ℝ) : ℝ := Real.sqrt (R ^ 2 - bandSq z)

private theorem bandWidth_pos {R : ℝ} (hR : 2 ≤ R) (z : ℝ) : 0 < bandWidth R z :=
  Real.sqrt_pos.mpr (by nlinarith [bandSq_le z])

private theorem contDiff_bandWidth {R : ℝ} (hR : 2 ≤ R) : ContDiff ℝ ∞ (bandWidth R) :=
  (contDiff_const.sub contDiff_bandSq).sqrt fun z => by nlinarith [bandSq_le z]

private theorem bandWidth_sq {R z : ℝ} (hR : 2 ≤ R) (hz : z ^ 2 ≤ 1) :
    bandWidth R z ^ 2 = R ^ 2 - z ^ 2 := by
  rw [bandWidth, bandSq_eq hz, Real.sq_sqrt (by nlinarith)]

private def bandChart (R : ℝ) (hR : 2 ≤ R) : (ℝ × ℝ) ≃ₘ[ℝ] Plane :=
  diffeoOfContDiff (fun z => Schoenflies.Plane.mk (z.1 * bandWidth R z.2) z.2)
    (fun y => (y 0 / bandWidth R (y 1), y 1))
    (by
      simp only [DifferentialGeometry.Topology.PlanarJordan.planeMk_eq_smul_add]
      exact ((contDiff_fst.mul ((contDiff_bandWidth hR).comp contDiff_snd)).smul
        contDiff_const).add (contDiff_snd.smul contDiff_const))
    (by
      have h0 := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := ∞)
      have h1 := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).contDiff (n := ∞)
      exact (h0.div ((contDiff_bandWidth hR).comp h1) fun y =>
        (bandWidth_pos hR _).ne').prodMk h1)
    (by
      intro z
      change (z.1 * bandWidth R z.2 / bandWidth R z.2, z.2) = z
      rw [mul_div_cancel_right₀ _ (bandWidth_pos hR _).ne'])
    (by
      intro y
      apply planeExt
      · change y 0 / bandWidth R (y 1) * bandWidth R (y 1) = y 0
        rw [div_mul_cancel₀ _ (bandWidth_pos hR _).ne']
      · rfl)

private theorem bandChart_apply {R : ℝ} (hR : 2 ≤ R) (z : ℝ × ℝ) :
    bandChart R hR z = Schoenflies.Plane.mk (z.1 * bandWidth R z.2) z.2 := rfl

private theorem bandWidth_zero {R : ℝ} (hR : 2 ≤ R) : bandWidth R 0 = R := by
  rw [bandWidth, bandSq_eq (by norm_num)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  exact Real.sqrt_sq (by linarith)

private theorem bandChart_corner {R : ℝ} (hR : 2 ≤ R) (a : ℝ) :
    bandChart R hR (a, 0) = Schoenflies.Plane.mk (a * R) 0 := by
  rw [bandChart_apply, bandWidth_zero hR]

private theorem bandChart_profile {R b : ℝ} (hR : 2 ≤ R) :
    ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ Ioo (a - 1 / 2) (a + 1 / 2) ×ˢ Ioo (-(1 / 2)) (1 / 2),
      bandChart R hR z ∈ halfDisc R b ↔ a * z.1 ≤ 1 ∧ 0 ≤ b * z.2 := by
  intro a ha z hz
  have ha2 : a ^ 2 = 1 := by
    rcases ha with rfl | rfl <;> norm_num
  have hz2 : z.2 ^ 2 ≤ 1 := by
    have := abs_lt.mpr ⟨hz.2.1, hz.2.2⟩
    nlinarith [abs_nonneg z.2, sq_abs z.2]
  have haz : 0 < a * z.1 := by
    rcases ha with rfl | rfl
    · linarith [hz.1.2]
    · linarith [hz.1.1]
  have hw := bandWidth_sq hR hz2
  have hpos : 0 < R ^ 2 - z.2 ^ 2 := by nlinarith
  rw [bandChart_apply]
  change ‖Schoenflies.Plane.mk (z.1 * bandWidth R z.2) z.2‖ ≤ R ∧ 0 ≤ b * z.2 ↔ _
  rw [← sq_le_sq₀ (norm_nonneg _) (by linarith), planeNormSq]
  change (z.1 * bandWidth R z.2) ^ 2 + z.2 ^ 2 ≤ R ^ 2 ∧ _ ↔ _
  rw [mul_pow, hw]
  have key : z.1 ^ 2 * (R ^ 2 - z.2 ^ 2) + z.2 ^ 2 ≤ R ^ 2 ↔ a * z.1 ≤ 1 := by
    have hz1 : z.1 ^ 2 = (a * z.1) ^ 2 := by rw [mul_pow, ha2, one_mul]
    rw [hz1]
    constructor
    · intro h
      have : (a * z.1) ^ 2 ≤ 1 := by
        by_contra hc
        have hc' := not_le.mp hc
        nlinarith
      nlinarith
    · intro h
      have : (a * z.1) ^ 2 ≤ 1 := by nlinarith
      nlinarith
  rw [key]


private theorem norm_eq_abs_of_coord_one_eq_zero {x : Plane} (hx : x 1 = 0) : ‖x‖ = |x 0| := by
  have hn := planeNormSq x
  rw [hx] at hn
  rw [← Real.sqrt_sq (norm_nonneg x), hn, ← sq_abs (x 0)]
  ring_nf
  exact Real.sqrt_sq (abs_nonneg _)

private theorem halfDiscCurve_regular {R b : ℝ} (hR : 0 < R) (hb : b ^ 2 = 1) :
    ∀ p ∈ semicircle R b ∪ axisSegment R,
      p ∉ ({Schoenflies.Plane.mk (-R) 0, Schoenflies.Plane.mk R 0} : Set Plane) →
      ∃ V : Set Plane, ∃ g : Plane → ℝ, IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧
        (∀ x ∈ V, x ∈ semicircle R b ∪ axisSegment R ↔ g x = 0) ∧ fderiv ℝ g p ≠ 0 := by
  have hb0 : b ≠ 0 := by rintro rfl; norm_num at hb
  have hcorner : ∀ x : Plane, x 1 = 0 → |x 0| = R →
      x ∈ ({Schoenflies.Plane.mk (-R) 0, Schoenflies.Plane.mk R 0} : Set Plane) := by
    intro x h1 h0
    rcases abs_eq hR.le |>.mp h0 with h | h
    · right; apply planeExt <;> simp [h, h1]
    · left; apply planeExt <;> simp [h, h1]
  rintro p (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩) hpc
  · have hpos : 0 < b * p 1 := by
      rcases lt_or_eq_of_le hp2 with h | h
      · exact h
      · exfalso
        have h1 : p 1 = 0 := by
          rcases mul_eq_zero.mp h.symm with h' | h'
          · exact absurd h' hb0
          · exact h'
        exact hpc (hcorner p h1 (by rw [← norm_eq_abs_of_coord_one_eq_zero h1, hp1]))
    refine ⟨{x | 0 < b * x 1}, fun x => ‖x‖ ^ 2 - R ^ 2,
      isOpen_lt continuous_const (continuous_const.mul (continuous_planeCoord 1)), hpos,
      (contDiff_norm_sq ℝ |>.sub contDiff_const).contDiffOn, ?_, ?_⟩
    · intro x hx
      constructor
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · change ‖x‖ ^ 2 - R ^ 2 = 0
          rw [h1]; ring
        · exfalso
          have : b * x 1 = 0 := by rw [h1, mul_zero]
          exact (ne_of_gt hx) this
      · intro h
        left
        refine ⟨?_, hx.le⟩
        have : ‖x‖ ^ 2 = R ^ 2 := by linarith
        exact (pow_left_inj₀ (norm_nonneg _) hR.le two_ne_zero).mp this
    · have hd : HasFDerivAt (fun x : Plane => ‖x‖ ^ 2 - R ^ 2) (2 • innerSL ℝ p) p :=
        (hasStrictFDerivAt_norm_sq p).hasFDerivAt.sub_const _
      rw [hd.fderiv]
      intro h
      have := congrArg (fun f : Plane →L[ℝ] ℝ => f p) h
      simp only [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
        zero_apply, hp1, nsmul_eq_mul, Nat.cast_ofNat] at this
      have : R ^ 2 = 0 := by linarith
      exact hR.ne' (pow_eq_zero_iff two_ne_zero |>.mp this)
  · have hlt : |p 0| < R := by
      rcases lt_or_eq_of_le hp2 with h | h
      · exact h
      · exact absurd (hcorner p hp1 h) hpc
    refine ⟨ball p (R - |p 0|), fun x => x 1, isOpen_ball, mem_ball_self (by linarith),
      ((EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).contDiff).contDiffOn, ?_, ?_⟩
    · intro x hx
      have hxR : ‖x‖ < R := by
        have h1 : ‖x‖ ≤ ‖p‖ + ‖x - p‖ := by
          have := norm_add_le p (x - p)
          rwa [add_sub_cancel] at this
        rw [norm_eq_abs_of_coord_one_eq_zero hp1] at h1
        rw [mem_ball, dist_eq_norm] at hx
        linarith
      constructor
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact absurd h1 hxR.ne
        · exact h1
      · intro h
        right
        refine ⟨h, ?_⟩
        rw [← norm_eq_abs_of_coord_one_eq_zero h]
        exact hxR.le
    · have hd : HasFDerivAt (fun x : Plane => x 1)
          (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) p :=
        (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt
      rw [hd.fderiv]
      intro h
      have := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 1 1)) h
      simp at this

private theorem isLocalDiffeomorphAt_of_det_ne_zero {F : Plane → Plane} (hF : ContDiff ℝ ∞ F)
    {x : Plane}
    (hx : LinearMap.det (fderiv ℝ F x : Plane →ₗ[ℝ] Plane) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ F x := by
  have hb : Function.Bijective (fderiv ℝ F x) :=
    (Module.End.isUnit_iff _).mp
      ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
  let A : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.ofBijective (fderiv ℝ F x)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
    F hF.contMDiff x A ((hF.differentiable (by simp) x).hasFDerivAt.hasMFDerivAt)

def tubeMap (Γ : ℝ → Plane) : Plane → Plane :=
  DifferentialGeometry.Topology.PlanarJordan.planeTube Γ
    (fun s => Schoenflies.Plane.perp (deriv Γ s))

theorem tubeMap_axis (Γ : ℝ → Plane) (s : ℝ) :
    tubeMap Γ (Schoenflies.Plane.mk s 0) = Γ s :=
  DifferentialGeometry.Topology.PlanarJordan.planeTube_mk _ _ s

private theorem contDiff_deriv_of_contDiff {Γ : ℝ → Plane} (hΓ : ContDiff ℝ ∞ Γ) :
    ContDiff ℝ ∞ (deriv Γ) :=
  (contDiff_infty_iff_deriv.mp hΓ).2

theorem contDiff_tubeMap {Γ : ℝ → Plane} (hΓ : ContDiff ℝ ∞ Γ) : ContDiff ℝ ∞ (tubeMap Γ) :=
  DifferentialGeometry.Topology.PlanarJordan.contDiff_planeTube hΓ
    (DifferentialGeometry.Topology.PlanarJordan.contDiff_planePerp.comp
      (contDiff_deriv_of_contDiff hΓ))

private theorem deriv_eq_of_straight {Γ : ℝ → Plane} {s₀ : ℝ}
    (hend : ∀ s, s₀ ≤ |s| → Γ s = Schoenflies.Plane.mk s 0) {s : ℝ} (hs : s₀ < |s|) :
    deriv Γ s = Schoenflies.Plane.mk 1 0 := by
  have hev : Γ =ᶠ[𝓝 s] fun t => Schoenflies.Plane.mk t 0 := by
    have hopen : IsOpen {t : ℝ | s₀ < |t|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hs] with t ht using hend t ht.le
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun t : ℝ => Schoenflies.Plane.mk t 0) (Schoenflies.Plane.mk 1 0) s := by
    have : (fun t : ℝ => Schoenflies.Plane.mk t 0) =
        fun t => t • Schoenflies.Plane.mk 1 0 := by
      funext t
      apply planeExt <;> simp
    rw [this]
    simpa using (hasDerivAt_id s).smul_const (Schoenflies.Plane.mk 1 0)
  exact hd.deriv

theorem tubeMap_eq_self {Γ : ℝ → Plane} {s₀ : ℝ}
    (hend : ∀ s, s₀ ≤ |s| → Γ s = Schoenflies.Plane.mk s 0) {x : Plane} (hx : s₀ < |x 0|) :
    tubeMap Γ x = x := by
  change Γ (x 0) + x 1 • Schoenflies.Plane.perp (deriv Γ (x 0)) = x
  rw [deriv_eq_of_straight hend hx, hend _ hx.le]
  apply planeExt <;> simp [Schoenflies.Plane.perp]

private theorem det_tubeMap_axis {Γ : ℝ → Plane} (hΓ : ContDiff ℝ ∞ Γ) (s : ℝ) :
    LinearMap.det (fderiv ℝ (tubeMap Γ) (Schoenflies.Plane.mk s 0) : Plane →ₗ[ℝ] Plane) =
      ‖deriv Γ s‖ ^ 2 := by
  have hν : Differentiable ℝ (fun s => Schoenflies.Plane.perp (deriv Γ s)) :=
    (DifferentialGeometry.Topology.PlanarJordan.contDiff_planePerp.comp
      (contDiff_deriv_of_contDiff hΓ)).differentiable (by simp)
  rw [tubeMap, DifferentialGeometry.Topology.PlanarJordan.det_fderiv_planeTube
    (hΓ.differentiable (by simp)) hν]
  simp

private theorem planeNorm_le (x : Plane) : ‖x‖ ≤ |x 0| + |x 1| := by
  have := DifferentialGeometry.Topology.PlanarJordan.planeDist_le_abs_add_abs x 0
  simpa using this

private theorem abs_coord_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le x i

private theorem norm_planeMk_zero_one : ‖Schoenflies.Plane.mk (0 : ℝ) 1‖ = 1 := by
  have h : ‖Schoenflies.Plane.mk (0 : ℝ) 1‖ ^ 2 = 1 ^ 2 := by
    rw [planeNormSq]
    change (0 : ℝ) ^ 2 + 1 ^ 2 = 1 ^ 2
    ring
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h

private theorem axisSegment_eq_image (R : ℝ) :
    axisSegment R = (fun s : ℝ => Schoenflies.Plane.mk s 0) '' Icc (-R) R := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x 0, abs_le.mp h2, planeExt rfl h1.symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨rfl, abs_le.mpr hs⟩

private theorem isCompact_axisSegment (R : ℝ) : IsCompact (axisSegment R) := by
  rw [axisSegment_eq_image]
  exact isCompact_Icc.image (continuous_planeMk.comp (continuous_id.prodMk continuous_const))

private theorem isLocalDiffeomorphAt_id_plane (x : Plane) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ (id : Plane → Plane) x := by
  apply isLocalDiffeomorphAt_of_det_ne_zero contDiff_id
  rw [fderiv_id]
  simp

theorem exists_axis_germ {Γ : ℝ → Plane} (hΓ : ContDiff ℝ ∞ Γ) (hinj : Function.Injective Γ)
    (himm : ∀ s, deriv Γ s ≠ 0) {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hend : ∀ s, s₀ ≤ |s| → Γ s = Schoenflies.Plane.mk s 0) :
    ∃ R : ℝ, 4 ≤ R ∧ s₀ + 2 ≤ R ∧ (∀ s, |s| ≤ s₀ → ‖Γ s‖ < R - 1) ∧
      ∃ c : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane Plane ∞,
        axisSegment R ⊆ c.source ∧ {x | R - 1 < ‖x‖} ⊆ c.source ∧
        (∀ s, |s| ≤ R → c (Schoenflies.Plane.mk s 0) = Γ s) ∧
        (∀ x, R - 1 < ‖x‖ → c x = x) := by
  classical
  set ν : ℝ → Plane := fun s => Schoenflies.Plane.perp (deriv Γ s) with hνdef
  have hνc : Continuous ν :=
    (DifferentialGeometry.Topology.PlanarJordan.contDiff_planePerp.comp
      (contDiff_deriv_of_contDiff hΓ)).continuous
  obtain ⟨Bγ, hBγ⟩ := (isCompact_Icc (a := -s₀) (b := s₀)).exists_bound_of_continuousOn
    hΓ.continuous.continuousOn
  obtain ⟨Bν, hBν⟩ := (isCompact_Icc (a := -s₀) (b := s₀)).exists_bound_of_continuousOn
    hνc.continuousOn
  set Mν : ℝ := max Bν 1 with hMν
  have hMν1 : 1 ≤ Mν := le_max_right _ _
  have hνbound : ∀ s, ‖ν s‖ ≤ Mν := by
    intro s
    by_cases hs : |s| ≤ s₀
    · exact (hBν s (abs_le.mp hs)).trans (le_max_left _ _)
    · have hs' : s₀ < |s| := not_le.mp hs
      have : ν s = Schoenflies.Plane.mk 0 1 := by
        simp only [hνdef, deriv_eq_of_straight hend hs']
        apply planeExt <;> simp [Schoenflies.Plane.perp]
      rw [this, norm_planeMk_zero_one]
      exact hMν1
  set R : ℝ := max Bγ 0 + Mν + s₀ + 3 with hRdef
  have hBγ0 : 0 ≤ max Bγ 0 := le_max_right _ _
  have hR4 : 4 ≤ R := by rw [hRdef]; linarith
  have hRs : s₀ + 2 ≤ R := by rw [hRdef]; linarith
  have hΓbound : ∀ s, |s| ≤ s₀ → ‖Γ s‖ < R - 1 := by
    intro s hs
    have := hBγ s (abs_le.mp hs)
    have := le_max_left Bγ 0
    rw [hRdef]
    linarith
  set T := tubeMap Γ with hTdef
  have hT : ContDiff ℝ ∞ T := contDiff_tubeMap hΓ
  have hKax : ∀ x ∈ axisSegment R, x = Schoenflies.Plane.mk (x 0) 0 :=
    fun x hx => planeExt rfl hx.1
  have hinjK : InjOn T (axisSegment R) := by
    intro x hx y hy hxy
    rw [hKax x hx, hKax y hy] at hxy ⊢
    rw [hTdef, tubeMap_axis, tubeMap_axis] at hxy
    rw [hinj hxy]
  have hdetK : ∀ x ∈ axisSegment R,
      LinearMap.det (fderiv ℝ T x : Plane →ₗ[ℝ] Plane) ≠ 0 := by
    intro x hx
    rw [hKax x hx, hTdef, det_tubeMap_axis hΓ]
    exact (pow_pos (norm_pos_iff.mpr (himm _)) 2).ne'
  have hloc : ∀ x ∈ axisSegment R, ∃ U ∈ 𝓝 x, InjOn T U := by
    intro x hx
    obtain ⟨φ, hxφ, hφ⟩ := isLocalDiffeomorphAt_of_det_ne_zero hT (hdetK x hx)
    refine ⟨φ.source, φ.open_source.mem_nhds hxφ, fun a ha b hb hab => ?_⟩
    apply φ.toPartialEquiv.injOn ha hb
    rw [← hφ ha, ← hφ hb]
    exact hab
  obtain ⟨N', hN'o, hKN', -, hN'inj⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_injOn_of_isCompact isOpen_univ
      hT.continuous.continuousOn (isCompact_axisSegment R) (subset_univ _) hinjK hloc
  set Ndet : Set Plane := {x | LinearMap.det (fderiv ℝ T x : Plane →ₗ[ℝ] Plane) ≠ 0}
  have hNdet : IsOpen Ndet := by
    have hc : Continuous fun x => (fderiv ℝ T x).det :=
      ContinuousLinearMap.continuous_det.comp (hT.continuous_fderiv (by simp))
    exact isOpen_ne_fun hc continuous_const
  set N₀ : Set Plane := N' ∩ Ndet ∩ {x | |x 1| < 1} with hN₀def
  have hN₀o : IsOpen N₀ :=
    (hN'o.inter hNdet).inter (isOpen_lt (continuous_abs.comp (continuous_planeCoord 1))
      continuous_const)
  set Ω : Set Plane := {x | R - 1 < ‖x‖} with hΩdef
  have hΩo : IsOpen Ω := isOpen_lt continuous_const continuous_norm
  set f : Plane → Plane := fun x => if x ∈ Ω then x else T x with hfdef
  have hTid : ∀ x : Plane, s₀ < |x 0| → T x = x := fun x hx => tubeMap_eq_self hend hx
  have hN₀Ω : ∀ x ∈ N₀, x ∈ Ω → T x = x := by
    intro x hx hxΩ
    apply hTid
    have h1 := planeNorm_le x
    have h2 : |x 1| < 1 := hx.2
    have h3 : R - 1 < ‖x‖ := hxΩ
    linarith
  have hfN₀ : ∀ x ∈ N₀, f x = T x := by
    intro x hx
    by_cases h : x ∈ Ω
    · simp only [hfdef, h, ↓reduceIte, hN₀Ω x hx h]
    · simp only [hfdef, h, ↓reduceIte]
  have hfΩ : ∀ x ∈ Ω, f x = x := by
    intro x hx
    simp only [hfdef, hx, ↓reduceIte]
  have hTbound : ∀ x ∈ N₀, T x ≠ x → ‖T x‖ < R - 1 := by
    intro x hx hTx
    have hx0 : |x 0| ≤ s₀ := by
      by_contra h
      exact hTx (hTid x (not_le.mp h))
    have hx1 : |x 1| < 1 := hx.2
    change ‖Γ (x 0) + x 1 • ν (x 0)‖ < R - 1
    calc ‖Γ (x 0) + x 1 • ν (x 0)‖ ≤ ‖Γ (x 0)‖ + |x 1| * ‖ν (x 0)‖ := by
          rw [← Real.norm_eq_abs, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ max Bγ 0 + 1 * Mν := by
          gcongr
          · exact (hBγ _ (abs_le.mp hx0)).trans (le_max_left _ _)
          · exact hνbound _
      _ < R - 1 := by rw [hRdef]; linarith
  have hlocW : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ f (N₀ ∪ Ω) := by
    rintro ⟨x, hx⟩
    rcases hx with hx | hx
    · have hev : f =ᶠ[𝓝 x] T := by
        filter_upwards [hN₀o.mem_nhds hx] with y hy using hfN₀ y hy
      exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev
        (isLocalDiffeomorphAt_of_det_ne_zero hT hx.1.2)
    · have hev : f =ᶠ[𝓝 x] id := by
        filter_upwards [hΩo.mem_nhds hx] with y hy using hfΩ y hy
      exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq hev
        (isLocalDiffeomorphAt_id_plane x)
  have hmixed : ∀ x ∈ N₀, ∀ y ∈ Ω, f x = f y → x = y := by
    intro x hx y hy hxy
    rw [hfN₀ x hx, hfΩ y hy] at hxy
    by_cases hTx : T x = x
    · rw [← hxy, hTx]
    · have h1 := hTbound x hx hTx
      have h2 : R - 1 < ‖y‖ := hy
      rw [hxy] at h1
      exact absurd h2 (not_lt.mpr h1.le)
  have hinjW : InjOn f (N₀ ∪ Ω) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hfN₀ x hx, hfN₀ y hy] at hxy
      exact hN'inj hx.1.1 hy.1.1 hxy
    · exact hmixed x hx y hy hxy
    · exact (hmixed y hy x hx hxy.symm).symm
    · rw [hfΩ x hx, hfΩ y hy] at hxy
      exact hxy
  obtain ⟨c, hcs, -, hcf⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn (hN₀o.union hΩo)
      hlocW hinjW
  have hKN₀ : axisSegment R ⊆ N₀ := fun x hx =>
    ⟨⟨hKN' hx, hdetK x hx⟩, by
      change |x 1| < 1
      rw [hx.1, abs_zero]
      exact one_pos⟩
  refine ⟨R, hR4, hRs, hΓbound, c, ?_, ?_, ?_, ?_⟩
  · rw [hcs]
    exact hKN₀.trans subset_union_left
  · rw [hcs]
    exact subset_union_right
  · intro s hs
    have hmem : Schoenflies.Plane.mk s 0 ∈ N₀ := hKN₀ ⟨rfl, hs⟩
    rw [hcf, hfN₀ _ hmem, hTdef, tubeMap_axis]
  · intro x hx
    rw [hcf, hfΩ x hx]

private theorem norm_planeMk_zero (y : ℝ) : ‖Schoenflies.Plane.mk 0 y‖ = |y| := by
  have h : ‖Schoenflies.Plane.mk 0 y‖ ^ 2 = |y| ^ 2 := by
    rw [planeNormSq, sq_abs]
    change (0 : ℝ) ^ 2 + y ^ 2 = y ^ 2
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp h

private theorem semicircle_subset_closedBall (R b : ℝ) : semicircle R b ⊆ closedBall 0 R :=
  fun _ hx => mem_closedBall_zero_iff.mpr hx.1.le

open DifferentialGeometry.Topology.PlanarJordan in
private theorem exists_half_extension {Γ : ℝ → Plane} {R b : ℝ} (hR : 4 ≤ R) (hb : b ^ 2 = 1)
    (hΓR : ∀ s, |s| ≤ R → ‖Γ s‖ ≤ R)
    (c : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane Plane ∞)
    (hcK : axisSegment R ⊆ c.source) (hcΩ : {x | R - 1 < ‖x‖} ⊆ c.source)
    (hcax : ∀ s, |s| ≤ R → c (Schoenflies.Plane.mk s 0) = Γ s)
    (hcid : ∀ x, R - 1 < ‖x‖ → c x = x) :
    ∃ F : Plane ≃ₘ[ℝ] Plane,
      F '' (semicircle R b ∪ axisSegment R) = semicircle R b ∪ Γ '' Icc (-R) R ∧
      F '' halfDisc R b = closure (inside (semicircle R b ∪ Γ '' Icc (-R) R)) ∧
      ∃ U : Set Plane, IsOpen U ∧ semicircle R b ∪ axisSegment R ⊆ U ∧ U ⊆ c.source ∧
        EqOn F c U := by
  have hR0 : 0 < R := by linarith
  set J₀ := semicircle R b ∪ axisSegment R with hJ₀def
  set J₁ := semicircle R b ∪ Γ '' Icc (-R) R with hJ₁def
  have hsemiΩ : semicircle R b ⊆ {x | R - 1 < ‖x‖} := by
    intro x hx
    change R - 1 < ‖x‖
    rw [hx.1]
    linarith
  have hJ₀s : J₀ ⊆ c.source := union_subset (hsemiΩ.trans hcΩ) hcK
  have hcJ : c '' J₀ = J₁ := by
    rw [hJ₀def, hJ₁def, image_union]
    congr 1
    · rw [image_congr (fun x hx => hcid x (hsemiΩ hx)), image_id']
    · rw [axisSegment_eq_image, image_image]
      exact image_congr fun s hs => hcax s (abs_le.mpr hs)
  have hJ₀ : IsJordanCurve J₀ := isJordanCurve_halfDiscCurve hR0 hb
  have hJ₁ : IsJordanCurve J₁ := by
    rw [← hcJ]
    exact c.toOpenPartialHomeomorph.isJordanCurve_image_of_subset_source hJ₀ hJ₀s
  have hJ₀ball : J₀ ⊆ closedBall 0 R := by
    refine union_subset (semicircle_subset_closedBall R b) fun x hx => ?_
    rw [mem_closedBall_zero_iff, norm_eq_abs_of_coord_one_eq_zero hx.1]
    exact hx.2
  have hJ₁ball : J₁ ⊆ closedBall 0 R := by
    refine union_subset (semicircle_subset_closedBall R b) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hΓR s (abs_le.mpr hs))
  have hy₀ : Schoenflies.Plane.mk 0 (b * R) ∈ J₀ := by
    left
    refine ⟨?_, ?_⟩
    · rw [norm_planeMk_zero, abs_mul, abs_of_pos hR0]
      rcases sq_eq_one_cases hb with rfl | rfl <;> simp
    · change 0 ≤ b * (b * R)
      have : b * (b * R) = b ^ 2 * R := by ring
      rw [this, hb, one_mul]
      exact hR0.le
  have hout : ∀ W : Set Plane, IsOpen W → J₀ ⊆ W →
      ∃ x ∈ W, x ∈ c.toOpenPartialHomeomorph.source ∧ x ∈ outside J₀ ∧
        c.toOpenPartialHomeomorph x ∈ outside J₁ := by
    intro W hW hJW
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW _ (hJW hy₀)
    set y₀ := Schoenflies.Plane.mk 0 (b * R)
    have hy₀n : ‖y₀‖ = R := by
      rw [norm_planeMk_zero, abs_mul, abs_of_pos hR0]
      rcases sq_eq_one_cases hb with rfl | rfl <;> simp
    set x := (1 + ε / (2 * R)) • y₀
    have hεR : 0 < ε / (2 * R) := by positivity
    have hxn : ‖x‖ = (1 + ε / (2 * R)) * R := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith), hy₀n]
    have hxR : R < ‖x‖ := by
      rw [hxn]
      nlinarith
    have hxW : x ∈ W := by
      apply hball
      rw [mem_ball, dist_eq_norm]
      have : x - y₀ = (ε / (2 * R)) • y₀ := by
        simp only [x, add_smul, one_smul, add_sub_cancel_left]
      rw [this, norm_smul, Real.norm_of_nonneg hεR.le, hy₀n]
      field_simp
      linarith
    have hxΩ : R - 1 < ‖x‖ := by linarith
    refine ⟨x, hxW, hcΩ hxΩ, mem_outside_of_lt_norm hR0.le hJ₀ball hxR, ?_⟩
    change c x ∈ outside J₁
    rw [hcid x hxΩ]
    exact mem_outside_of_lt_norm hR0.le hJ₁ball hxR
  obtain ⟨V, hVo, hJV, hVs, hVimg⟩ :=
    exists_closure_inside_iff_of_outside hJ₀ hJ₁ c.toOpenPartialHomeomorph hJ₀s hcJ hout
  set c' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict c V hVo with hc'def
  have hc's : c'.source = c.source ∩ V := rfl
  have hc'eq : ∀ x, c' x = c x := fun x => rfl
  have hJ₀c' : J₀ ⊆ c'.source := fun x hx => ⟨hJ₀s hx, hJV hx⟩
  have hc'img : c'.toOpenPartialHomeomorph.IsImage (closure (inside J₀))
      (closure (inside J₁)) := by
    intro x hx
    exact hVimg x hx.2
  have hcorner : ∀ a : ℝ, bandChart R (by linarith) (a, 0) = Schoenflies.Plane.mk (a * R) 0 :=
    fun a => bandChart_corner _ a
  have hpoints : ({bandChart R (by linarith) (-1, 0), bandChart R (by linarith) (1, 0)} :
      Set Plane) ⊆ c'.source := by
    rw [hcorner, hcorner, neg_one_mul, one_mul]
    rintro _ (rfl | rfl)
    · exact hJ₀c' (Or.inr ⟨rfl, by simp [abs_of_pos hR0]⟩)
    · exact hJ₀c' (Or.inr ⟨rfl, by simp [abs_of_pos hR0]⟩)
  have hreg : ∀ p ∈ J₀, p ∉ ({bandChart R (by linarith) (-1, 0),
      bandChart R (by linarith) (1, 0)} : Set Plane) →
      ∃ V : Set Plane, ∃ g : Plane → ℝ, IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧
        (∀ x ∈ V, x ∈ J₀ ↔ g x = 0) ∧ fderiv ℝ g p ≠ 0 := by
    rw [hcorner, hcorner, neg_one_mul, one_mul]
    exact halfDiscCurve_regular hR0 hb
  have hprofile := bandChart_profile (b := b) (by linarith : (2 : ℝ) ≤ R)
  rw [← closure_inside_halfDiscCurve hR0 hb] at hprofile
  obtain ⟨F, hFJ, hFD, U, hUo, hJU, hUs, hFU⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_band_corner_curve
      (bandChart R (by linarith)) c' hb (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) c'.open_source hpoints subset_rfl hJ₀ hJ₁ hJ₀c' hc'img
      hreg (Or.inl hprofile)
  refine ⟨F, hFJ, ?_, U, hUo, hJU, hUs.trans inter_subset_left, fun x hx => (hFU hx).trans
    (hc'eq x)⟩
  rw [← closure_inside_halfDiscCurve hR0 hb]
  exact hFD

private theorem mem_halfDisc_one {R : ℝ} {x : Plane} : x ∈ halfDisc R 1 ↔ ‖x‖ ≤ R ∧ 0 ≤ x 1 := by
  simp [halfDisc]

private theorem mem_halfDisc_neg_one {R : ℝ} {x : Plane} :
    x ∈ halfDisc R (-1) ↔ ‖x‖ ≤ R ∧ x 1 ≤ 0 := by
  simp [halfDisc]

private theorem halfDisc_inter {R : ℝ} : halfDisc R 1 ∩ halfDisc R (-1) = axisSegment R := by
  ext x
  rw [mem_inter_iff, mem_halfDisc_one, mem_halfDisc_neg_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h3⟩
    have hx : x 1 = 0 := le_antisymm h3 h2
    exact ⟨hx, by rw [← norm_eq_abs_of_coord_one_eq_zero hx]; exact h1⟩
  · rintro ⟨h1, h2⟩
    have hn : ‖x‖ ≤ R := by rw [norm_eq_abs_of_coord_one_eq_zero h1]; exact h2
    exact ⟨⟨hn, h1.ge⟩, hn, h1.le⟩

private theorem isArcBetween_image_Icc {Γ : ℝ → Plane} (hΓ : Continuous Γ)
    (hinj : Function.Injective Γ)
    {R : ℝ} (hR : 0 < R) :
    Schoenflies.IsArcBetween (Γ '' Icc (-R) R) (Γ (-R)) (Γ R) := by
  refine ⟨fun t => Γ (-R + 2 * R * t), ?_, ?_, ?_, ?_, ?_⟩
  · exact (hΓ.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  · intro s _ t _ hst
    have h := hinj hst
    have : 2 * R * s = 2 * R * t := by linarith
    exact mul_left_cancel₀ (by positivity) this
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨-R + 2 * R * t, ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(s + R) / (2 * R), ⟨div_nonneg (by linarith [hs.1]) (by positivity), ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]
        linarith [hs.2]
      · change Γ (-R + 2 * R * ((s + R) / (2 * R))) = Γ s
        congr 1
        field_simp
        ring
  · simp
  · change Γ (-R + 2 * R * 1) = Γ R
    congr 1
    ring

theorem exists_diffeomorph_axis_line {Γ : ℝ → Plane} (hΓ : ContDiff ℝ ∞ Γ)
    (hinj : Function.Injective Γ) (himm : ∀ s, deriv Γ s ≠ 0) {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hend : ∀ s, s₀ ≤ |s| → Γ s = Schoenflies.Plane.mk s 0) :
    ∃ Q : Plane ≃ₘ[ℝ] Plane, (∃ K : Set Plane, IsCompact K ∧ ∀ x, x ∉ K → Q x = x) ∧
      ∀ s, Q (Schoenflies.Plane.mk s 0) = Γ s := by
  classical
  obtain ⟨R, hR4, hRs, hΓs, c, hcK, hcΩ, hcax, hcid⟩ := exists_axis_germ hΓ hinj himm hs₀ hend
  have hR0 : 0 < R := by linarith
  have hΓR : ∀ s, |s| ≤ R → ‖Γ s‖ ≤ R := by
    intro s hs
    by_cases h : s₀ ≤ |s|
    · rw [hend s h, norm_eq_abs_of_coord_one_eq_zero rfl]
      exact hs
    · exact (hΓs s (not_le.mp h).le).le.trans (by linarith)
  have hΓlt : ∀ s, |s| < R → ‖Γ s‖ < R := by
    intro s hs
    by_cases h : s₀ ≤ |s|
    · rw [hend s h, norm_eq_abs_of_coord_one_eq_zero rfl]
      exact hs
    · exact (hΓs s (not_le.mp h).le).trans (by linarith)
  have hΓpm : ∀ a : ℝ, |a| = R → Γ a = Schoenflies.Plane.mk a 0 :=
    fun a ha => hend a (by rw [ha]; linarith)
  obtain ⟨F₁, hF₁J, hF₁D, U₁, hU₁o, hJU₁, hU₁s, hF₁U⟩ :=
    exists_half_extension (b := 1) hR4 (by norm_num) hΓR c hcK hcΩ hcax hcid
  obtain ⟨F₂, hF₂J, hF₂D, U₂, hU₂o, hJU₂, hU₂s, hF₂U⟩ :=
    exists_half_extension (b := -1) hR4 (by norm_num) hΓR c hcK hcΩ hcax hcid
  set P₁ := Γ '' Icc (-R) R with hP₁def
  set p : Plane := Schoenflies.Plane.mk (-R) 0 with hpdef
  set q : Plane := Schoenflies.Plane.mk R 0 with hqdef
  have hΓp : Γ (-R) = p := hΓpm (-R) (by rw [abs_neg, abs_of_pos hR0])
  have hΓq : Γ R = q := hΓpm R (abs_of_pos hR0)
  have hP₁arc : Schoenflies.IsArcBetween P₁ p q := by
    rw [← hΓp, ← hΓq]
    exact isArcBetween_image_Icc hΓ.continuous hinj hR0
  have hC := isJordanCurve_sphere' hR0
  have hcut := isCutPair_semicircles hR0
  have hP₁C : P₁ \ {p, q} ⊆ inside (sphere (0 : Plane) R) := by
    rw [inside_sphere hR0]
    rintro _ ⟨⟨s, hs, rfl⟩, hne⟩
    have hs' : |s| < R := by
      rcases lt_or_eq_of_le (abs_le.mpr hs) with h | h
      · exact h
      · exfalso
        apply hne
        rcases abs_eq hR0.le |>.mp h with rfl | rfl
        · exact Or.inr hΓq
        · exact Or.inl hΓp
    exact mem_ball_zero_iff.mpr (hΓlt s hs')
  obtain ⟨hD₁cover, hD₁inter⟩ :=
    DifferentialGeometry.Topology.PlanarJordan.closed_crosscut_regions hC hP₁arc hcut hP₁C
  obtain ⟨-, -, hD₁trace₁, hD₁trace₂⟩ :=
    DifferentialGeometry.Topology.PlanarJordan.crosscut_regions hC hP₁arc hcut hP₁C
  rw [inside_sphere hR0, sphere_union_ball] at hD₁cover
  set D₀₁ := halfDisc R 1 with hD₀₁def
  set D₀₂ := halfDisc R (-1) with hD₀₂def
  set J₁₁ := semicircle R 1 ∪ P₁ with hJ₁₁def
  set J₁₂ := semicircle R (-1) ∪ P₁ with hJ₁₂def
  set D₁₁ := closure (inside J₁₁) with hD₁₁def
  set D₁₂ := closure (inside J₁₂) with hD₁₂def
  set Ω : Set Plane := {x | R - 1 < ‖x‖} with hΩdef
  have hΩo : IsOpen Ω := isOpen_lt continuous_const continuous_norm
  have hJ₁₁ : IsJordanCurve J₁₁ := by
    rw [← hF₁J]
    exact DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image F₁.toHomeomorph
      (isJordanCurve_halfDiscCurve hR0 (by norm_num))
  have hJ₁₂ : IsJordanCurve J₁₂ := by
    rw [← hF₂J]
    exact DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image F₂.toHomeomorph
      (isJordanCurve_halfDiscCurve hR0 (by norm_num))
  have hcl₁₁ : D₁₁ = inside J₁₁ ∪ J₁₁ :=
    (Schoenflies.IsRegionOf.inside J₁₁).closure_eq (Schoenflies.jordan_curve_theorem hJ₁₁)
  have hcl₁₂ : D₁₂ = inside J₁₂ ∪ J₁₂ :=
    (Schoenflies.IsRegionOf.inside J₁₂).closure_eq (Schoenflies.jordan_curve_theorem hJ₁₂)
  have hin₁₁o : IsOpen (inside J₁₁) := Schoenflies.isOpen_inside hJ₁₁.isClosed
  have hin₁₂o : IsOpen (inside J₁₂) := Schoenflies.isOpen_inside hJ₁₂.isClosed
  have hD₁₁c : IsClosed D₁₁ := isClosed_closure
  have hD₁₂c : IsClosed D₁₂ := isClosed_closure
  have hD₁₁ball : D₁₁ ⊆ closedBall 0 R := hD₁cover ▸ subset_union_left
  have hD₁₂ball : D₁₂ ⊆ closedBall 0 R := hD₁cover ▸ subset_union_right
  have hD₀₁ball : D₀₁ ⊆ closedBall 0 R := fun x hx => mem_closedBall_zero_iff.mpr hx.1
  have hD₀₂ball : D₀₂ ⊆ closedBall 0 R := fun x hx => mem_closedBall_zero_iff.mpr hx.1
  have hP₁D₁₁ : P₁ ⊆ D₁₁ := hD₁inter ▸ inter_subset_left
  have hJ₀₁U : semicircle R 1 ∪ axisSegment R ⊆ U₁ := hJU₁
  have hJ₀₂U : semicircle R (-1) ∪ axisSegment R ⊆ U₂ := hJU₂
  have hF₁c : ∀ x ∈ U₁, F₁ x = c x := fun x hx => hF₁U hx
  have hF₂c : ∀ x ∈ U₂, F₂ x = c x := fun x hx => hF₂U hx
  have hcΩid : ∀ x ∈ Ω, c x = x := fun x hx => hcid x hx
  have hcsymmΩ : ∀ y ∈ Ω, c.toPartialEquiv.symm y = y := by
    intro y hy
    have h := c.toPartialEquiv.left_inv (hcΩ hy)
    have h2 : c.toPartialEquiv y = y := hcid y hy
    rw [h2] at h
    exact h
  have hF₁s : ∀ y ∈ F₁ '' U₁, F₁.symm y = c.toPartialEquiv.symm y := by
    rintro _ ⟨z, hz, rfl⟩
    rw [F₁.symm_apply_apply]
    have h := c.toPartialEquiv.left_inv (hU₁s hz)
    have h2 : c.toPartialEquiv z = F₁ z := (hF₁c z hz).symm
    rw [h2] at h
    exact h.symm
  have hF₂s : ∀ y ∈ F₂ '' U₂, F₂.symm y = c.toPartialEquiv.symm y := by
    rintro _ ⟨z, hz, rfl⟩
    rw [F₂.symm_apply_apply]
    have h := c.toPartialEquiv.left_inv (hU₂s hz)
    have h2 : c.toPartialEquiv z = F₂ z := (hF₂c z hz).symm
    rw [h2] at h
    exact h.symm
  have hFU₁o : IsOpen (F₁ '' U₁) := F₁.toHomeomorph.isOpenMap _ hU₁o
  have hFU₂o : IsOpen (F₂ '' U₂) := F₂.toHomeomorph.isOpenMap _ hU₂o
  have hJ₁₁FU : J₁₁ ⊆ F₁ '' U₁ := by rw [← hF₁J]; exact image_mono hJ₀₁U
  have hJ₁₂FU : J₁₂ ⊆ F₂ '' U₂ := by rw [← hF₂J]; exact image_mono hJ₀₂U
  have hcaxis : ∀ z ∈ axisSegment R, c z ∈ P₁ := by
    intro z hz
    have hz' : z = Schoenflies.Plane.mk (z 0) 0 := planeExt rfl hz.1
    rw [hz', hcax _ hz.2]
    exact ⟨z 0, abs_le.mp hz.2, rfl⟩
  have hP₁corner : ∀ y ∈ P₁, R ≤ ‖y‖ → y 1 = 0 := by
    rintro _ ⟨s, hs, rfl⟩ hy
    have hs' : |s| = R := by
      by_contra h
      exact absurd hy (not_le.mpr (hΓlt s (lt_of_le_of_ne (abs_le.mpr hs) h)))
    rw [hΓpm s hs']
    rfl
  have hax₁ : axisSegment R ⊆ D₀₁ := by
    rw [← halfDisc_inter]; exact inter_subset_left
  have hax₂ : axisSegment R ⊆ D₀₂ := by
    rw [← halfDisc_inter]; exact inter_subset_right
  set Qf : Plane → Plane := fun x => if x ∈ D₀₁ then F₁ x else if x ∈ D₀₂ then F₂ x else x
    with hQfdef
  set Qg : Plane → Plane := fun y =>
    if y ∈ D₁₁ then F₁.symm y else if y ∈ D₁₂ then F₂.symm y else y with hQgdef
  have hQfc : ∀ y, (y ∈ D₀₁ → y ∈ U₁) → (y ∉ D₀₁ → y ∈ D₀₂ → y ∈ U₂) →
      (y ∉ D₀₁ → y ∉ D₀₂ → y ∈ Ω) → Qf y = c y := by
    intro y h1 h2 h3
    by_cases hy1 : y ∈ D₀₁
    · simp only [hQfdef, hy1, ↓reduceIte]
      exact hF₁c y (h1 hy1)
    · by_cases hy2 : y ∈ D₀₂
      · simp only [hQfdef, hy1, hy2, ↓reduceIte]
        exact hF₂c y (h2 hy1 hy2)
      · simp only [hQfdef, hy1, hy2, ↓reduceIte]
        exact (hcΩid y (h3 hy1 hy2)).symm
  have hQgc : ∀ y, (y ∈ D₁₁ → y ∈ F₁ '' U₁) → (y ∉ D₁₁ → y ∈ D₁₂ → y ∈ F₂ '' U₂) →
      (y ∉ D₁₁ → y ∉ D₁₂ → y ∈ Ω) → Qg y = c.toPartialEquiv.symm y := by
    intro y h1 h2 h3
    by_cases hy1 : y ∈ D₁₁
    · simp only [hQgdef, hy1, ↓reduceIte]
      exact hF₁s y (h1 hy1)
    · by_cases hy2 : y ∈ D₁₂
      · simp only [hQgdef, hy1, hy2, ↓reduceIte]
        exact hF₂s y (h2 hy1 hy2)
      · simp only [hQgdef, hy1, hy2, ↓reduceIte]
        exact (hcsymmΩ y (h3 hy1 hy2)).symm
  have hcCD : ∀ x ∈ c.source, ContDiffAt ℝ ∞ c x := fun x hx =>
    (contMDiffOn_iff_contDiffOn.mp c.contMDiffOn_toFun).contDiffAt (c.open_source.mem_nhds hx)
  have hcsCD : ∀ y ∈ c.target, ContDiffAt ℝ ∞ c.toPartialEquiv.symm y := fun y hy =>
    (contMDiffOn_iff_contDiffOn.mp c.contMDiffOn_invFun).contDiffAt (c.open_target.mem_nhds hy)
  have hF₁cd : ContDiff ℝ ∞ F₁ := contMDiff_iff_contDiff.mp F₁.contMDiff
  have hF₂cd : ContDiff ℝ ∞ F₂ := contMDiff_iff_contDiff.mp F₂.contMDiff
  have hF₁scd : ContDiff ℝ ∞ F₁.symm := contMDiff_iff_contDiff.mp F₁.symm.contMDiff
  have hF₂scd : ContDiff ℝ ∞ F₂.symm := contMDiff_iff_contDiff.mp F₂.symm.contMDiff
  have hFU₁t : F₁ '' U₁ ⊆ c.target := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hF₁c z hz]
    exact c.toPartialEquiv.map_source (hU₁s hz)
  have hFU₂t : F₂ '' U₂ ⊆ c.target := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hF₂c z hz]
    exact c.toPartialEquiv.map_source (hU₂s hz)
  have hlo : IsOpen {y : Plane | y 1 < 0} := isOpen_lt (continuous_planeCoord 1) continuous_const
  have hup : IsOpen {y : Plane | 0 < y 1} := isOpen_lt continuous_const (continuous_planeCoord 1)
  have hout : IsOpen {y : Plane | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hcornerax : ∀ x : Plane, ‖x‖ = R → x 1 = 0 → x ∈ axisSegment R := fun x h1 h2 =>
    ⟨h2, by rw [← norm_eq_abs_of_coord_one_eq_zero h2, h1]⟩
  have hQf : ContDiff ℝ ∞ Qf := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_trichotomy ‖x‖ R with hxR | hxR | hxR
    · rcases lt_trichotomy (x 1) 0 with hx1 | hx1 | hx1
      · have hev : Qf =ᶠ[𝓝 x] F₂ := by
          filter_upwards [(isOpen_ball.inter hlo).mem_nhds
            ⟨mem_ball_zero_iff.mpr hxR, hx1⟩] with y hy
          have hy1 : y ∉ D₀₁ := fun h => absurd (mem_halfDisc_one.mp h).2 (not_le.mpr hy.2)
          have hy2 : y ∈ D₀₂ := mem_halfDisc_neg_one.mpr
            ⟨(mem_ball_zero_iff.mp hy.1).le, (show y 1 < 0 from hy.2).le⟩
          simp only [hQfdef, hy1, hy2, ↓reduceIte]
        exact hF₂cd.contDiffAt.congr_of_eventuallyEq hev
      · have hxax : x ∈ axisSegment R :=
          ⟨hx1, by rw [← norm_eq_abs_of_coord_one_eq_zero hx1]; exact hxR.le⟩
        have hev : Qf =ᶠ[𝓝 x] c := by
          filter_upwards [hU₁o.mem_nhds (hJ₀₁U (Or.inr hxax)),
            hU₂o.mem_nhds (hJ₀₂U (Or.inr hxax)),
            isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxR)] with y hy1 hy2 hy3
          refine hQfc y (fun _ => hy1) (fun _ _ => hy2) fun h1 h2 => ?_
          exfalso
          have hyR : ‖y‖ ≤ R := (mem_ball_zero_iff.mp hy3).le
          rcases le_total 0 (y 1) with h | h
          · exact h1 (mem_halfDisc_one.mpr ⟨hyR, h⟩)
          · exact h2 (mem_halfDisc_neg_one.mpr ⟨hyR, h⟩)
        exact (hcCD x (hU₁s (hJ₀₁U (Or.inr hxax)))).congr_of_eventuallyEq hev
      · have hev : Qf =ᶠ[𝓝 x] F₁ := by
          filter_upwards [(isOpen_ball.inter hup).mem_nhds
            ⟨mem_ball_zero_iff.mpr hxR, hx1⟩] with y hy
          have hy1 : y ∈ D₀₁ := mem_halfDisc_one.mpr
            ⟨(mem_ball_zero_iff.mp hy.1).le, (show 0 < y 1 from hy.2).le⟩
          simp only [hQfdef, hy1, ↓reduceIte]
        exact hF₁cd.contDiffAt.congr_of_eventuallyEq hev
    · have hxΩ : x ∈ Ω := by change R - 1 < ‖x‖; linarith
      rcases lt_trichotomy (x 1) 0 with hx1 | hx1 | hx1
      · have hxs : x ∈ semicircle R (-1) := ⟨hxR, by linarith⟩
        have hev : Qf =ᶠ[𝓝 x] c := by
          filter_upwards [hU₂o.mem_nhds (hJ₀₂U (Or.inl hxs)), hΩo.mem_nhds hxΩ,
            hlo.mem_nhds hx1] with y hy1 hy2 hy3
          refine hQfc y (fun h => ?_) (fun _ _ => hy1) fun _ _ => hy2
          exact absurd (mem_halfDisc_one.mp h).2 (not_le.mpr hy3)
        exact (hcCD x (hU₂s (hJ₀₂U (Or.inl hxs)))).congr_of_eventuallyEq hev
      · have hxax := hcornerax x hxR hx1
        have hev : Qf =ᶠ[𝓝 x] c := by
          filter_upwards [hU₁o.mem_nhds (hJ₀₁U (Or.inr hxax)),
            hU₂o.mem_nhds (hJ₀₂U (Or.inr hxax)), hΩo.mem_nhds hxΩ] with y hy1 hy2 hy3
          exact hQfc y (fun _ => hy1) (fun _ _ => hy2) fun _ _ => hy3
        exact (hcCD x (hU₁s (hJ₀₁U (Or.inr hxax)))).congr_of_eventuallyEq hev
      · have hxs : x ∈ semicircle R 1 := ⟨hxR, by linarith⟩
        have hev : Qf =ᶠ[𝓝 x] c := by
          filter_upwards [hU₁o.mem_nhds (hJ₀₁U (Or.inl hxs)), hΩo.mem_nhds hxΩ,
            hup.mem_nhds hx1] with y hy1 hy2 hy3
          refine hQfc y (fun _ => hy1) (fun _ h => ?_) fun _ _ => hy2
          exact absurd (mem_halfDisc_neg_one.mp h).2 (not_le.mpr hy3)
        exact (hcCD x (hU₁s (hJ₀₁U (Or.inl hxs)))).congr_of_eventuallyEq hev
    · have hev : Qf =ᶠ[𝓝 x] id := by
        filter_upwards [hout.mem_nhds hxR] with y hy
        have hy1 : y ∉ D₀₁ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₀₁ball h)) (not_le.mpr hy)
        have hy2 : y ∉ D₀₂ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₀₂ball h)) (not_le.mpr hy)
        simp only [hQfdef, hy1, hy2, ↓reduceIte, id]
      exact contDiff_id.contDiffAt.congr_of_eventuallyEq hev
  have hsemi₁J : semicircle R 1 ⊆ J₁₁ := subset_union_left
  have hsemi₂J : semicircle R (-1) ⊆ J₁₂ := subset_union_left
  have hD₁₁sph : ∀ z, ‖z‖ = R → z ∈ D₁₁ → 0 ≤ z 1 := by
    intro z hz h
    have : z ∈ D₁₁ ∩ sphere 0 R := ⟨h, mem_sphere_zero_iff_norm.mpr hz⟩
    rw [hD₁trace₁] at this
    simpa using this.2
  have hD₁₂sph : ∀ z, ‖z‖ = R → z ∈ D₁₂ → z 1 ≤ 0 := by
    intro z hz h
    have : z ∈ D₁₂ ∩ sphere 0 R := ⟨h, mem_sphere_zero_iff_norm.mpr hz⟩
    rw [hD₁trace₂] at this
    have h2 := this.2
    simp only [neg_one_mul, neg_nonneg] at h2
    exact h2
  have hQg : ContDiff ℝ ∞ Qg := by
    rw [contDiff_iff_contDiffAt]
    intro y
    rcases lt_trichotomy ‖y‖ R with hyR | hyR | hyR
    · by_cases hin1 : y ∈ inside J₁₁
      · have hev : Qg =ᶠ[𝓝 y] F₁.symm := by
          filter_upwards [hin₁₁o.mem_nhds hin1] with z hz
          have hz1 : z ∈ D₁₁ := subset_closure hz
          simp only [hQgdef, hz1, ↓reduceIte]
        exact hF₁scd.contDiffAt.congr_of_eventuallyEq hev
      · by_cases hin2 : y ∈ inside J₁₂
        · have hev : Qg =ᶠ[𝓝 y] F₂.symm := by
            filter_upwards [hin₁₂o.mem_nhds hin2] with z hz
            have hz2 : z ∈ D₁₂ := subset_closure hz
            have hz1 : z ∉ D₁₁ := by
              intro h
              have hzP : z ∈ P₁ := hD₁inter ▸ ⟨h, hz2⟩
              exact hz.1 (subset_union_right hzP)
            simp only [hQgdef, hz1, hz2, ↓reduceIte]
          exact hF₂scd.contDiffAt.congr_of_eventuallyEq hev
        · have hyP : y ∈ P₁ := by
            have hyB : y ∈ closedBall (0 : Plane) R := mem_closedBall_zero_iff.mpr hyR.le
            rw [← hD₁cover, hcl₁₁, hcl₁₂] at hyB
            rcases hyB with (h | h | h) | (h | h | h)
            · exact absurd h hin1
            · exact absurd h.1 hyR.ne
            · exact h
            · exact absurd h hin2
            · exact absurd h.1 hyR.ne
            · exact h
          have hy₁ : y ∈ F₁ '' U₁ := hJ₁₁FU (subset_union_right hyP)
          have hy₂ : y ∈ F₂ '' U₂ := hJ₁₂FU (subset_union_right hyP)
          have hev : Qg =ᶠ[𝓝 y] c.toPartialEquiv.symm := by
            filter_upwards [hFU₁o.mem_nhds hy₁, hFU₂o.mem_nhds hy₂,
              isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hyR)] with z hz1 hz2 hz3
            refine hQgc z (fun _ => hz1) (fun _ _ => hz2) fun h1 h2 => ?_
            exfalso
            have hzB : z ∈ closedBall (0 : Plane) R :=
              mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hz3).le
            rw [← hD₁cover] at hzB
            rcases hzB with h | h
            · exact h1 h
            · exact h2 h
          exact (hcsCD y (hFU₁t hy₁)).congr_of_eventuallyEq hev
    · have hyΩ : y ∈ Ω := by change R - 1 < ‖y‖; linarith
      rcases lt_trichotomy (y 1) 0 with hy1 | hy1 | hy1
      · have hys : y ∈ semicircle R (-1) := ⟨hyR, by linarith⟩
        have hy₂ : y ∈ F₂ '' U₂ := hJ₁₂FU (hsemi₂J hys)
        have hyD : y ∉ D₁₁ := fun h => absurd (hD₁₁sph y hyR h) (not_le.mpr hy1)
        have hev : Qg =ᶠ[𝓝 y] c.toPartialEquiv.symm := by
          filter_upwards [hFU₂o.mem_nhds hy₂, hΩo.mem_nhds hyΩ,
            hD₁₁c.isOpen_compl.mem_nhds hyD] with z hz1 hz2 hz3
          exact hQgc z (fun h => absurd h hz3) (fun _ _ => hz1) fun _ _ => hz2
        exact (hcsCD y (hFU₂t hy₂)).congr_of_eventuallyEq hev
      · have hys₁ : y ∈ semicircle R 1 := ⟨hyR, by rw [hy1]; simp⟩
        have hys₂ : y ∈ semicircle R (-1) := ⟨hyR, by rw [hy1]; simp⟩
        have hy₁ : y ∈ F₁ '' U₁ := hJ₁₁FU (hsemi₁J hys₁)
        have hy₂ : y ∈ F₂ '' U₂ := hJ₁₂FU (hsemi₂J hys₂)
        have hev : Qg =ᶠ[𝓝 y] c.toPartialEquiv.symm := by
          filter_upwards [hFU₁o.mem_nhds hy₁, hFU₂o.mem_nhds hy₂, hΩo.mem_nhds hyΩ] with
            z hz1 hz2 hz3
          exact hQgc z (fun _ => hz1) (fun _ _ => hz2) fun _ _ => hz3
        exact (hcsCD y (hFU₁t hy₁)).congr_of_eventuallyEq hev
      · have hys : y ∈ semicircle R 1 := ⟨hyR, by linarith⟩
        have hy₁ : y ∈ F₁ '' U₁ := hJ₁₁FU (hsemi₁J hys)
        have hyD : y ∉ D₁₂ := fun h => absurd (hD₁₂sph y hyR h) (not_le.mpr hy1)
        have hev : Qg =ᶠ[𝓝 y] c.toPartialEquiv.symm := by
          filter_upwards [hFU₁o.mem_nhds hy₁, hΩo.mem_nhds hyΩ,
            hD₁₂c.isOpen_compl.mem_nhds hyD] with z hz1 hz2 hz3
          exact hQgc z (fun _ => hz1) (fun _ h => absurd h hz3) fun _ _ => hz2
        exact (hcsCD y (hFU₁t hy₁)).congr_of_eventuallyEq hev
    · have hev : Qg =ᶠ[𝓝 y] id := by
        filter_upwards [hout.mem_nhds hyR] with z hz
        have hz1 : z ∉ D₁₁ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₁₁ball h)) (not_le.mpr hz)
        have hz2 : z ∉ D₁₂ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₁₂ball h)) (not_le.mpr hz)
        simp only [hQgdef, hz1, hz2, ↓reduceIte, id]
      exact contDiff_id.contDiffAt.congr_of_eventuallyEq hev
  have hF₁D₀ : ∀ x ∈ D₀₁, F₁ x ∈ D₁₁ := fun x hx => hF₁D ▸ mem_image_of_mem F₁ hx
  have hF₂D₀ : ∀ x ∈ D₀₂, F₂ x ∈ D₁₂ := fun x hx => hF₂D ▸ mem_image_of_mem F₂ hx
  have hF₁D₁ : ∀ y ∈ D₁₁, F₁.symm y ∈ D₀₁ := by
    intro y hy
    rw [← hF₁D] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [F₁.symm_apply_apply]
    exact hx
  have hF₂D₁ : ∀ y ∈ D₁₂, F₂.symm y ∈ D₀₂ := by
    intro y hy
    rw [← hF₂D] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [F₂.symm_apply_apply]
    exact hx
  have hgf : ∀ x, Qg (Qf x) = x := by
    intro x
    by_cases hx1 : x ∈ D₀₁
    · have h := hF₁D₀ x hx1
      simp only [hQfdef, hQgdef, hx1, h, ↓reduceIte, F₁.symm_apply_apply]
    · by_cases hx2 : x ∈ D₀₂
      · have h := hF₂D₀ x hx2
        have hn : F₂ x ∉ D₁₁ := by
          intro hF
          have hP : F₂ x ∈ P₁ := hD₁inter ▸ ⟨hF, h⟩
          have hJ : F₂ x ∈ F₂ '' (semicircle R (-1) ∪ axisSegment R) :=
            hF₂J ▸ subset_union_right hP
          obtain ⟨z, hz, hzx⟩ := hJ
          rw [F₂.injective hzx] at hz
          rcases hz with hz | hz
          · have hxU : x ∈ U₂ := hJ₀₂U (Or.inl hz)
            have hxΩ : x ∈ Ω := by change R - 1 < ‖x‖; rw [hz.1]; linarith
            rw [hF₂c x hxU, hcΩid x hxΩ] at hP
            have h0 := hP₁corner x hP hz.1.ge
            exact hx1 (hax₁ (hcornerax x hz.1 h0))
          · exact hx1 (hax₁ hz)
        simp only [hQfdef, hQgdef, hx1, hx2, h, hn, ↓reduceIte, F₂.symm_apply_apply]
      · have hxR : R < ‖x‖ := by
          by_contra hle
          have hle' : ‖x‖ ≤ R := not_lt.mp hle
          rcases le_total 0 (x 1) with h | h
          · exact hx1 (mem_halfDisc_one.mpr ⟨hle', h⟩)
          · exact hx2 (mem_halfDisc_neg_one.mpr ⟨hle', h⟩)
        have h1 : x ∉ D₁₁ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₁₁ball h)) (not_le.mpr hxR)
        have h2 : x ∉ D₁₂ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₁₂ball h)) (not_le.mpr hxR)
        simp only [hQfdef, hQgdef, hx1, hx2, h1, h2, ↓reduceIte]
  have hfg : ∀ y, Qf (Qg y) = y := by
    intro y
    by_cases hy1 : y ∈ D₁₁
    · have h := hF₁D₁ y hy1
      simp only [hQfdef, hQgdef, hy1, h, ↓reduceIte, F₁.apply_symm_apply]
    · by_cases hy2 : y ∈ D₁₂
      · have h := hF₂D₁ y hy2
        have hn : F₂.symm y ∉ D₀₁ := by
          intro hz
          have hax : F₂.symm y ∈ axisSegment R := halfDisc_inter ▸ ⟨hz, h⟩
          have hU : F₂.symm y ∈ U₂ := hJ₀₂U (Or.inr hax)
          have hP := hcaxis _ hax
          rw [← hF₂c _ hU, F₂.apply_symm_apply] at hP
          exact hy1 (hP₁D₁₁ hP)
        simp only [hQfdef, hQgdef, hy1, hy2, h, hn, ↓reduceIte, F₂.apply_symm_apply]
      · have hyR : R < ‖y‖ := by
          by_contra hle
          have hyB : y ∈ closedBall (0 : Plane) R := mem_closedBall_zero_iff.mpr (not_lt.mp hle)
          rw [← hD₁cover] at hyB
          rcases hyB with h | h
          · exact hy1 h
          · exact hy2 h
        have h1 : y ∉ D₀₁ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₀₁ball h)) (not_le.mpr hyR)
        have h2 : y ∉ D₀₂ := fun h =>
          absurd (mem_closedBall_zero_iff.mp (hD₀₂ball h)) (not_le.mpr hyR)
        simp only [hQfdef, hQgdef, hy1, hy2, h1, h2, ↓reduceIte]
  refine ⟨diffeoOfContDiff Qf Qg hQf hQg hgf hfg, ⟨closedBall 0 R, isCompact_closedBall _ _,
    fun x hx => ?_⟩, fun s => ?_⟩
  · have hxR : R < ‖x‖ := not_le.mp fun h => hx (mem_closedBall_zero_iff.mpr h)
    have h1 : x ∉ D₀₁ := fun h =>
      absurd (mem_closedBall_zero_iff.mp (hD₀₁ball h)) (not_le.mpr hxR)
    have h2 : x ∉ D₀₂ := fun h =>
      absurd (mem_closedBall_zero_iff.mp (hD₀₂ball h)) (not_le.mpr hxR)
    change Qf x = x
    simp only [hQfdef, h1, h2, ↓reduceIte]
  · change Qf _ = _
    by_cases hs : |s| ≤ R
    · have hax : Schoenflies.Plane.mk s 0 ∈ axisSegment R := ⟨rfl, hs⟩
      have h1 := hax₁ hax
      simp only [hQfdef, h1, ↓reduceIte]
      rw [hF₁c _ (hJ₀₁U (Or.inr hax)), hcax s hs]
    · have hsR : R < |s| := not_le.mp hs
      have hn : R < ‖Schoenflies.Plane.mk s 0‖ := by
        rw [norm_eq_abs_of_coord_one_eq_zero rfl]
        exact hsR
      have h1 : Schoenflies.Plane.mk s 0 ∉ D₀₁ := fun h =>
        absurd (mem_closedBall_zero_iff.mp (hD₀₁ball h)) (not_le.mpr hn)
      have h2 : Schoenflies.Plane.mk s 0 ∉ D₀₂ := fun h =>
        absurd (mem_closedBall_zero_iff.mp (hD₀₂ball h)) (not_le.mpr hn)
      simp only [hQfdef, h1, h2, ↓reduceIte]
      exact (hend s (by linarith)).symm

def sqCoord (X : ℝ) : ℝ := Real.tan (Real.pi * (X - 1 / 2))

def sqCoordInv (y : ℝ) : ℝ := 1 / 2 + Real.arctan y / Real.pi

private theorem sqCoordInv_mem (y : ℝ) : sqCoordInv y ∈ Ioo (0 : ℝ) 1 := by
  have h1 := Real.arctan_lt_pi_div_two y
  have h2 := Real.neg_pi_div_two_lt_arctan y
  have hpi := Real.pi_pos
  constructor
  · unfold sqCoordInv
    have : -(1 / 2) < Real.arctan y / Real.pi := by
      rw [lt_div_iff₀ hpi]; linarith
    linarith
  · unfold sqCoordInv
    have : Real.arctan y / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ hpi]; linarith
    linarith

theorem sqCoord_sqCoordInv (y : ℝ) : sqCoord (sqCoordInv y) = y := by
  unfold sqCoord sqCoordInv
  have : Real.pi * (1 / 2 + Real.arctan y / Real.pi - 1 / 2) = Real.arctan y := by
    field_simp
    ring
  rw [this, Real.tan_arctan]

private theorem sqCoord_arg_mem {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    Real.pi * (X - 1 / 2) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hpi := Real.pi_pos
  constructor <;> nlinarith [hX.1, hX.2]

theorem sqCoordInv_sqCoord {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) : sqCoordInv (sqCoord X) = X := by
  unfold sqCoordInv sqCoord
  rw [Real.arctan_tan (sqCoord_arg_mem hX).1 (sqCoord_arg_mem hX).2]
  field_simp
  ring

private theorem cos_sqCoord_pos {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    0 < Real.cos (Real.pi * (X - 1 / 2)) :=
  Real.cos_pos_of_mem_Ioo (sqCoord_arg_mem hX)

private theorem hasDerivAt_sqCoord {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt sqCoord (1 / Real.cos (Real.pi * (X - 1 / 2)) ^ 2 * Real.pi) X := by
  have h1 : HasDerivAt (fun X : ℝ => Real.pi * (X - 1 / 2)) Real.pi X := by
    simpa using ((hasDerivAt_id X).sub_const (1 / 2 : ℝ)).const_mul Real.pi
  exact (Real.hasDerivAt_tan (cos_sqCoord_pos hX).ne').comp X h1

private theorem contDiffOn_sqCoord : ContDiffOn ℝ ∞ sqCoord (Ioo 0 1) := by
  intro X hX
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiff ℝ ∞ (fun X : ℝ => Real.pi * (X - 1 / 2)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  exact (Real.contDiffAt_tan.mpr (cos_sqCoord_pos hX).ne').comp X h1.contDiffAt

private theorem contDiff_sqCoordInv : ContDiff ℝ ∞ sqCoordInv :=
  contDiff_const.add (Real.contDiff_arctan.div_const _)

private theorem hasDerivAt_sqCoordInv (y : ℝ) :
    HasDerivAt sqCoordInv (1 / (1 + y ^ 2) / Real.pi) y := by
  have := ((Real.hasDerivAt_arctan y).div_const Real.pi).const_add (1 / 2 : ℝ)
  exact this

private theorem sqCoord_half : sqCoord (1 / 2) = 0 := by
  simp [sqCoord]

private theorem strictMono_sqCoordInv : StrictMono sqCoordInv := by
  intro a b hab
  unfold sqCoordInv
  have := Real.arctan_strictMono hab
  have hpi := Real.pi_pos
  have : Real.arctan a / Real.pi < Real.arctan b / Real.pi := div_lt_div_of_pos_right this hpi
  linarith

private theorem sqCoordInv_neg (y : ℝ) : sqCoordInv (-y) = 1 - sqCoordInv y := by
  unfold sqCoordInv
  rw [Real.arctan_neg]
  ring

theorem mem_openSquare {z : ℂ} : z ∈ openSquare ↔ z.re ∈ Ioo (0 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) 1 :=
  Iff.rfl

def squareChart : OpenPartialHomeomorph ℂ ℂ where
  toFun z := (sqCoord z.re : ℂ) + (sqCoord z.im : ℂ) * Complex.I
  invFun w := (sqCoordInv w.re : ℂ) + (sqCoordInv w.im : ℂ) * Complex.I
  source := openSquare
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := by
    rw [mem_openSquare]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add]
    exact ⟨sqCoordInv_mem _, sqCoordInv_mem _⟩
  left_inv' z hz := by
    rw [mem_openSquare] at hz
    apply Complex.ext <;>
      simp [sqCoordInv_sqCoord hz.1, sqCoordInv_sqCoord hz.2]
  right_inv' w _ := by
    apply Complex.ext <;> simp [sqCoord_sqCoordInv]
  open_source := IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  open_target := isOpen_univ
  continuousOn_toFun := by
    have h1 : ContinuousOn (fun z : ℂ => sqCoord z.re) openSquare :=
      contDiffOn_sqCoord.continuousOn.comp Complex.continuous_re.continuousOn
        fun z hz => (mem_openSquare.mp hz).1
    have h2 : ContinuousOn (fun z : ℂ => sqCoord z.im) openSquare :=
      contDiffOn_sqCoord.continuousOn.comp Complex.continuous_im.continuousOn
        fun z hz => (mem_openSquare.mp hz).2
    exact (Complex.continuous_ofReal.comp_continuousOn h1).add
      ((Complex.continuous_ofReal.comp_continuousOn h2).mul continuousOn_const)
  continuousOn_invFun := by
    have h1 := contDiff_sqCoordInv.continuous.comp Complex.continuous_re
    have h2 := contDiff_sqCoordInv.continuous.comp Complex.continuous_im
    exact ((Complex.continuous_ofReal.comp h1).add
      ((Complex.continuous_ofReal.comp h2).mul continuous_const)).continuousOn

theorem squareChart_apply (z : ℂ) :
    squareChart z = (sqCoord z.re : ℂ) + (sqCoord z.im : ℂ) * Complex.I := rfl

theorem squareChart_symm_apply (w : ℂ) :
    squareChart.symm w = (sqCoordInv w.re : ℂ) + (sqCoordInv w.im : ℂ) * Complex.I := rfl

theorem contMDiffOn_squareChart :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ squareChart squareChart.source := by
  rw [contMDiffOn_iff_contDiffOn]
  have h1 : ContDiffOn ℝ ∞ (fun z : ℂ => sqCoord z.re) openSquare :=
    contDiffOn_sqCoord.comp Complex.reCLM.contDiff.contDiffOn
      fun z hz => (mem_openSquare.mp hz).1
  have h2 : ContDiffOn ℝ ∞ (fun z : ℂ => sqCoord z.im) openSquare :=
    contDiffOn_sqCoord.comp Complex.imCLM.contDiff.contDiffOn
      fun z hz => (mem_openSquare.mp hz).2
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul contDiffOn_const)

theorem contMDiffOn_squareChart_symm :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ squareChart.symm squareChart.target := by
  rw [contMDiffOn_iff_contDiffOn]
  have h1 := contDiff_sqCoordInv.comp Complex.reCLM.contDiff
  have h2 := contDiff_sqCoordInv.comp Complex.imCLM.contDiff
  exact ((Complex.ofRealCLM.contDiff.comp h1).add
    ((Complex.ofRealCLM.contDiff.comp h2).mul contDiff_const)).contDiffOn

private def planeOfComplexLinear : ℂ ≃ₗ[ℝ] Plane where
  toFun z := Schoenflies.Plane.mk z.im z.re
  invFun x := ⟨x 1, x 0⟩
  map_add' z w := by apply planeExt <;> simp
  map_smul' r z := by apply planeExt <;> simp
  left_inv z := by apply Complex.ext <;> simp
  right_inv x := by apply planeExt <;> simp

private def planeOfComplex : ℂ ≃L[ℝ] Plane := planeOfComplexLinear.toContinuousLinearEquiv

private theorem planeOfComplex_apply (z : ℂ) :
    planeOfComplex z = Schoenflies.Plane.mk z.im z.re := rfl

private theorem planeOfComplex_real_mul_I (s : ℝ) :
    planeOfComplex ((s : ℂ) * Complex.I) = Schoenflies.Plane.mk s 0 := by
  rw [planeOfComplex_apply]
  apply planeExt <;> simp

theorem exists_isotopy_square_arc {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (hinj : InjOn γ (Icc 0 1)) (himm : ∀ t, deriv γ t ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hend : ∀ t, t ≤ δ ∨ 1 - δ ≤ t → γ t = (1 / 2 : ℂ) + (t : ℂ) * Complex.I)
    (hin : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ openSquare) :
    ∃ H : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ => H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (∃ K : Set ℂ, IsCompact K ∧ K ⊆ openSquare ∧ ∀ p z, z ∉ K → H p z = z) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, H 1 ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = γ t := by
  classical
  set δ' : ℝ := min δ (1 / 4) with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'q : δ' ≤ 1 / 4 := min_le_right _ _
  have hmem1 : 1 - δ' ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set s₀ : ℝ := max (sqCoord (1 - δ')) 0 with hs₀def
  have hs₀ : 0 ≤ s₀ := le_max_right _ _
  have hτmem : ∀ s, sqCoordInv s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨(sqCoordInv_mem s).1.le, (sqCoordInv_mem s).2.le⟩
  have huend : ∀ s, s₀ ≤ |s| →
      γ (sqCoordInv s) = (1 / 2 : ℂ) + (sqCoordInv s : ℂ) * Complex.I := by
    intro s hs
    apply hend
    rcases le_abs'.mp hs with h | h
    · left
      have h1 : s ≤ -sqCoord (1 - δ') := by
        have := le_max_left (sqCoord (1 - δ')) 0
        linarith
      have h2 := strictMono_sqCoordInv.monotone h1
      rw [sqCoordInv_neg, sqCoordInv_sqCoord hmem1] at h2
      linarith
    · right
      have h1 : sqCoord (1 - δ') ≤ s := le_trans (le_max_left _ _) h
      have h2 := strictMono_sqCoordInv.monotone h1
      rw [sqCoordInv_sqCoord hmem1] at h2
      linarith
  set u : ℝ → ℂ := fun s => γ (sqCoordInv s) with hudef
  have hu : ContDiff ℝ ∞ u := hγ.comp contDiff_sqCoordInv
  have husq : ∀ s, u s ∈ openSquare := fun s => hin _ (sqCoordInv_mem s)
  set ΓC : ℝ → ℂ := fun s => squareChart (u s) with hΓCdef
  have hΓC : ContDiff ℝ ∞ ΓC :=
    (contMDiffOn_iff_contDiffOn.mp contMDiffOn_squareChart).comp_contDiff hu husq
  set ΓP : ℝ → Plane := fun s => planeOfComplex (ΓC s) with hΓPdef
  have hΓP : ContDiff ℝ ∞ ΓP := planeOfComplex.contDiff.comp hΓC
  have hΓPinj : Function.Injective ΓP := by
    intro s s' h
    have h1 : ΓC s = ΓC s' := planeOfComplex.injective h
    have h2 : u s = u s' := squareChart.injOn (husq s) (husq s') h1
    have h3 : sqCoordInv s = sqCoordInv s' := hinj (hτmem s) (hτmem s') h2
    exact strictMono_sqCoordInv.injective h3
  have hΓPimm : ∀ s, deriv ΓP s ≠ 0 := by
    intro s
    set τ' : ℝ := 1 / (1 + s ^ 2) / Real.pi with hτ'def
    have hτ'0 : τ' ≠ 0 := by
      rw [hτ'def]
      have : 0 < 1 + s ^ 2 := by positivity
      exact div_ne_zero (div_ne_zero one_ne_zero this.ne') Real.pi_pos.ne'
    have hu' : HasDerivAt u (τ' • deriv γ (sqCoordInv s)) s :=
      ((hγ.differentiable (by simp)).differentiableAt.hasDerivAt).scomp s
        (hasDerivAt_sqCoordInv s)
    set v : ℂ := τ' • deriv γ (sqCoordInv s) with hvdef
    have hv0 : v ≠ 0 := smul_ne_zero hτ'0 (himm _)
    have hre : HasDerivAt (fun s => (u s).re) v.re s :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hu'
    have him : HasDerivAt (fun s => (u s).im) v.im s :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hu'
    set kr : ℝ := 1 / Real.cos (Real.pi * ((u s).re - 1 / 2)) ^ 2 * Real.pi with hkrdef
    set ki : ℝ := 1 / Real.cos (Real.pi * ((u s).im - 1 / 2)) ^ 2 * Real.pi with hkidef
    have hkr : kr ≠ 0 := by
      rw [hkrdef]
      exact mul_ne_zero (one_div_ne_zero (pow_ne_zero 2
        (cos_sqCoord_pos (mem_openSquare.mp (husq s)).1).ne')) Real.pi_pos.ne'
    have hki : ki ≠ 0 := by
      rw [hkidef]
      exact mul_ne_zero (one_div_ne_zero (pow_ne_zero 2
        (cos_sqCoord_pos (mem_openSquare.mp (husq s)).2).ne')) Real.pi_pos.ne'
    have hsr : HasDerivAt (fun s => sqCoord (u s).re) (kr * v.re) s :=
      HasDerivAt.comp (h := fun s => (u s).re) s
        (hasDerivAt_sqCoord (mem_openSquare.mp (husq s)).1) hre
    have hsi : HasDerivAt (fun s => sqCoord (u s).im) (ki * v.im) s :=
      HasDerivAt.comp (h := fun s => (u s).im) s
        (hasDerivAt_sqCoord (mem_openSquare.mp (husq s)).2) him
    have hP : HasDerivAt ΓP (Schoenflies.Plane.mk (ki * v.im) (kr * v.re)) s := by
      have hfun : ΓP = fun s => (sqCoord (u s).im) • Schoenflies.Plane.mk 1 0 +
          (sqCoord (u s).re) • Schoenflies.Plane.mk 0 1 := by
        funext s
        simp only [hΓPdef, hΓCdef, squareChart_apply, planeOfComplex_apply]
        apply planeExt <;> simp
      rw [hfun]
      have := (hsi.smul_const (Schoenflies.Plane.mk (1 : ℝ) 0)).add
        (hsr.smul_const (Schoenflies.Plane.mk (0 : ℝ) 1))
      convert this using 1
      apply planeExt <;> simp
    rw [hP.deriv]
    intro h0
    have h1 : ki * v.im = 0 := congrArg (fun x : Plane => x 0) h0
    have h2 : kr * v.re = 0 := congrArg (fun x : Plane => x 1) h0
    apply hv0
    apply Complex.ext
    · simpa [hkr] using h2
    · simpa [hki] using h1
  have hΓPend : ∀ s, s₀ ≤ |s| → ΓP s = Schoenflies.Plane.mk s 0 := by
    intro s hs
    have h1 : u s = (1 / 2 : ℂ) + (sqCoordInv s : ℂ) * Complex.I := huend s hs
    have hre : (u s).re = 1 / 2 := by rw [h1]; simp
    have him : (u s).im = sqCoordInv s := by rw [h1]; simp
    have hC : ΓC s = (s : ℂ) * Complex.I := by
      simp only [hΓCdef, squareChart_apply, hre, him, sqCoord_half, sqCoord_sqCoordInv,
        Complex.ofReal_zero, zero_add]
    simp only [hΓPdef, hC, planeOfComplex_real_mul_I]
  obtain ⟨Q, ⟨K, hK, hQK⟩, hQax⟩ :=
    exists_diffeomorph_axis_line hΓP hΓPinj hΓPimm hs₀ hΓPend
  set QC : ℂ ≃ₘ[ℝ] ℂ :=
    (planeOfComplex.toDiffeomorph.trans Q).trans planeOfComplex.symm.toDiffeomorph with hQCdef
  have hQCapp : ∀ z, QC z = planeOfComplex.symm (Q (planeOfComplex z)) := fun z => rfl
  set K' : Set ℂ := planeOfComplex.symm '' K with hK'def
  have hK' : IsCompact K' := hK.image planeOfComplex.symm.continuous
  have hQCfix : ∀ z, z ∉ K' → QC z = z := by
    intro z hz
    have hzK : planeOfComplex z ∉ K := fun h =>
      hz ⟨planeOfComplex z, h, planeOfComplex.symm_apply_apply z⟩
    rw [hQCapp, hQK _ hzK, planeOfComplex.symm_apply_apply]
  have hQCax : ∀ s : ℝ, QC ((s : ℂ) * Complex.I) = squareChart (u s) := by
    intro s
    rw [hQCapp, planeOfComplex_real_mul_I, hQax]
    exact planeOfComplex.symm_apply_apply _
  have hsupp : HasCompactSupport (fun z => QC z - z) :=
    HasCompactSupport.intro hK' fun z hz => by rw [hQCfix z hz, sub_self]
  obtain ⟨D, hD, hDi, hD0, hD1, L, hL, hDfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_compactly_supported_planar_isotopy QC hsupp
  obtain ⟨J, hJ, hJi, hJe, hKJ, hKJs, hJfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_chart_family
      (M := ℂ) (I := 𝓘(ℝ, ℂ)) (P := ℝ) squareChart rfl contMDiffOn_squareChart
      contMDiffOn_squareChart_symm D hD hDi hL (fun p z hz => hDfix p z hz)
  have hJcd : ContDiff ℝ ∞ (fun q : ℝ × ℂ => J q.1 q.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hJ
    exact contMDiff_iff_contDiff.mp hJ
  have hJicd : ContDiff ℝ ∞ (fun q : ℝ × ℂ => (J q.1).symm q.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hJi
    exact contMDiff_iff_contDiff.mp hJi
  have hflip : ContDiff ℝ ∞ (fun q : ℝ × ℂ => ((1 - q.1, q.2) : ℝ × ℂ)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  refine ⟨fun p => J (1 - p), hJcd.comp hflip, hJicd.comp hflip, ?_,
    ⟨squareChart.symm '' L, hKJ, hKJs, fun p z hz => (hJfix (1 - p) z hz).1⟩, ?_⟩
  · apply Diffeomorph.ext
    intro x
    change J (1 - 0) x = x
    rw [sub_zero, (hJe 1 x).1, hD1]
    unfold DifferentialGeometry.Topology.Manifold.extendChartById
    split_ifs with hx
    · exact squareChart.left_inv hx
    · rfl
  · intro t ht
    change J (1 - 1) _ = γ t
    rw [sub_self, (hJe 0 _).1, hD0]
    unfold DifferentialGeometry.Topology.Manifold.extendChartById
    by_cases hto : t ∈ Ioo (0 : ℝ) 1
    · have hre : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 := by simp
      have him : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      have hmem : (1 / 2 : ℂ) + (t : ℂ) * Complex.I ∈ squareChart.source := by
        change _ ∈ openSquare
        rw [mem_openSquare, hre, him]
        exact ⟨⟨by norm_num, by norm_num⟩, hto⟩
      simp only [hmem, ↓reduceIte]
      have hψ : squareChart ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
          (sqCoord t : ℂ) * Complex.I := by
        rw [squareChart_apply, hre, him, sqCoord_half, Complex.ofReal_zero, zero_add]
      rw [hψ, hQCax]
      simp only [hudef, sqCoordInv_sqCoord hto]
      exact squareChart.left_inv (hin t hto)
    · have hnot : (1 / 2 : ℂ) + (t : ℂ) * Complex.I ∉ squareChart.source := by
        intro h
        change _ ∈ openSquare at h
        rw [mem_openSquare] at h
        apply hto
        simpa using h.2
      simp only [hnot, ↓reduceIte]
      have ht01 : t = 0 ∨ t = 1 := by
        by_contra h
        push Not at h
        exact hto ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1), lt_of_le_of_ne ht.2 h.2⟩
      rcases ht01 with rfl | rfl
      · exact (hend 0 (Or.inl hδ.le)).symm
      · exact (hend 1 (Or.inr (by linarith))).symm

end GC.Seifert
