import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChart

/-!
# E2 kernel, part 1: adapted charts of a smooth domain of a one-manifold (lane S-EDGE-INT)

Draft 74, package E2 (`finite_interval_circle_components74`). For a smooth one-manifold `Base`
(model `𝓡 1`) and a set `C` with the local defining-function data of `EdgeBundle.cbase_domain`
(at every frontier point a smooth `φ` with `dφ ≠ 0` and `C ∩ U = {φ ≥ 0} ∩ U`), every point `x ∈ C`
has a chart `ψ` of the maximal atlas of `Base` in which `C` is exactly the closed half-line
`{0 ≤ ψ y 0}` (`exists_adaptedChart_EIM`). These are the charts of the half-line atlas of `↥C`
(`EdgeBaseAtlasEIM.lean`).

* `exists_chart_of_regular_EIM`: the inverse function theorem on `Base` (the tree's
  `isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv`) turns a regular function into a
  chart whose first coordinate is the function;
* `exists_chart_pos_EIM`: a chart with positive first coordinate inside a given open set (interior
  points of `C`);
* `exists_adaptedChart_EIM`: the combination.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The coordinate `x ↦ x 0` as a continuous linear equivalence `ℝ¹ ≃L ℝ`. -/
def coordCLE_EIM : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (LinearEquiv.mk
    { toFun := fun x => x 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (fun r => EuclideanSpace.single 0 r)
    (fun x => by
      ext i
      fin_cases i
      simp)
    (fun r => by simp)).toContinuousLinearEquiv

@[simp] theorem coordCLE_EIM_apply (x : EuclideanSpace ℝ (Fin 1)) : coordCLE_EIM x = x 0 := rfl

@[simp] theorem coordCLE_EIM_symm_apply (r : ℝ) :
    coordCLE_EIM.symm r = EuclideanSpace.single 0 r := rfl

/-- A nonzero linear map `ℝ¹ → ℝ` is invertible. -/
theorem isInvertible_of_ne_zero_EIM {D : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ} (hD : D ≠ 0) :
    D.IsInvertible := by
  obtain ⟨v, hv⟩ : ∃ v, D v ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousLinearMap.ext h)
  have hsingle : ∀ w : EuclideanSpace ℝ (Fin 1), w = w 0 • EuclideanSpace.single 0 (1 : ℝ) := by
    intro w
    ext i
    fin_cases i
    simp
  have hform : ∀ w : EuclideanSpace ℝ (Fin 1),
      D w = w 0 * D (EuclideanSpace.single 0 (1 : ℝ)) := by
    intro w
    conv_lhs => rw [hsingle w]
    rw [map_smul, smul_eq_mul]
  have hne : D (EuclideanSpace.single 0 (1 : ℝ)) ≠ 0 := by
    intro h
    apply hv
    rw [hform, h, mul_zero]
  have hinj : LinearMap.ker (D : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℝ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have h0 : w 0 = 0 := by
      have : w 0 * D (EuclideanSpace.single 0 (1 : ℝ)) = 0 := (hform w).symm.trans hw
      exact (mul_eq_zero.mp this).resolve_right hne
    rw [hsingle w, h0, zero_smul]
  have hsurj : LinearMap.range (D : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℝ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    refine ⟨(r / D (EuclideanSpace.single 0 (1 : ℝ))) • EuclideanSpace.single 0 (1 : ℝ), ?_⟩
    rw [ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
  exact ⟨ContinuousLinearEquiv.ofBijective D hinj hsurj, rfl⟩

variable {Base : Type*} [TopologicalSpace Base]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base] [IsManifold (𝓡 1) ∞ Base]

/-- **Adapted chart from a regular function.** Near a point `c` where `φ` is smooth with nonzero
derivative, a chart of the maximal atlas whose first coordinate is exactly `φ`. -/
theorem exists_chart_of_regular_EIM {U : Set Base} (hU : IsOpen U) {φ : Base → ℝ}
    (hφ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U) {c : Base} (hc : c ∈ U)
    (hd : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)),
      ψ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base ∧ c ∈ ψ.source ∧ ψ.source ⊆ U ∧
        ∀ y ∈ ψ.source, ψ y 0 = φ y := by
  have hinv : (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c).IsInvertible :=
    isInvertible_of_ne_zero_EIM (D := mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c) hd
  obtain ⟨Φ, hcΦ, heq⟩ :=
    DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      hU hc hφ hinv
  let Φ' : OpenPartialHomeomorph Base ℝ := Φ.toOpenPartialHomeomorph.restrOpen U hU
  let ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)) :=
    Φ'.trans coordCLE_EIM.symm.toHomeomorph.toOpenPartialHomeomorph
  have hψs : ψ.source = Φ.source ∩ U := by
    simp [ψ, Φ']
  have hΦs : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ Φ Φ.source := Φ.contMDiffOn_toFun
  have hΦi : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ Φ.symm Φ.target := Φ.contMDiffOn_invFun
  refine ⟨ψ, ?_, by rw [hψs]; exact ⟨hcΦ, hc⟩, ?_, ?_⟩
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · have h1 : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ Φ ψ.source :=
        hΦs.mono (by rw [hψs]; exact inter_subset_left)
      exact ((coordCLE_EIM.symm.contDiff.contMDiff).comp_contMDiffOn h1).congr fun y hy => rfl
    · have hmaps : MapsTo (fun z : EuclideanSpace ℝ (Fin 1) => coordCLE_EIM z) ψ.target
          Φ.target := by
        intro z hz
        have hz' : coordCLE_EIM.symm.toHomeomorph.toOpenPartialHomeomorph.symm z ∈ Φ'.target :=
          hz.2
        have : coordCLE_EIM z ∈ Φ'.target := hz'
        exact this.1
      have h2 : ContMDiffOn (𝓡 1) (𝓡 1) ∞
          (fun z : EuclideanSpace ℝ (Fin 1) => Φ.symm (coordCLE_EIM z)) ψ.target :=
        hΦi.comp (coordCLE_EIM.contDiff.contMDiff).contMDiffOn hmaps
      exact h2.congr fun z hz => rfl
  · intro y hy
    rw [hψs] at hy
    exact hy.2
  · intro y hy
    rw [hψs] at hy
    change (coordCLE_EIM.symm (Φ y)) 0 = φ y
    rw [coordCLE_EIM_symm_apply]
    simp [heq hy.1]

/-- **A positive chart at any point.** A chart of the maximal atlas around `x` inside `W` whose
first coordinate is positive. -/
theorem exists_chart_pos_EIM {W : Set Base} (hW : IsOpen W) {x : Base} (hx : x ∈ W) :
    ∃ ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)),
      ψ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base ∧ x ∈ ψ.source ∧ ψ.source ⊆ W ∧
        ∀ y ∈ ψ.source, 0 < ψ y 0 := by
  let c₀ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)) :=
    chartAt (EuclideanSpace ℝ (Fin 1)) x
  have hc₀ : c₀ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base := IsManifold.chart_mem_maximalAtlas x
  set a : EuclideanSpace ℝ (Fin 1) := c₀ x with ha
  let v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (1 - a 0)
  let S : Set Base := W ∩ (c₀.source ∩ c₀ ⁻¹' Metric.ball a (1 / 2))
  have hS : IsOpen S := hW.inter (c₀.isOpen_inter_preimage Metric.isOpen_ball)
  have hxS : x ∈ S := ⟨hx, mem_chart_source _ x, by simp [ha]⟩
  let T : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)) :=
    (Homeomorph.addRight v).toOpenPartialHomeomorph
  let ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)) := (c₀.restrOpen S hS).trans T
  have hψs : ψ.source = c₀.source ∩ S := by
    simp [ψ, T]
  have hψv : ∀ y, ψ y = c₀ y + v := fun y => rfl
  refine ⟨ψ, ?_, by rw [hψs]; exact ⟨mem_chart_source _ x, hxS⟩, ?_, ?_⟩
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · have h1 : ContMDiffOn (𝓡 1) (𝓡 1) ∞ c₀ ψ.source :=
        (contMDiffOn_of_mem_maximalAtlas hc₀).mono (by rw [hψs]; exact inter_subset_left)
      have hT : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : EuclideanSpace ℝ (Fin 1) => z + v) :=
        (contDiff_id.add contDiff_const).contMDiff
      exact (hT.comp_contMDiffOn h1).congr fun y hy => rfl
    · have hmaps : MapsTo (fun z : EuclideanSpace ℝ (Fin 1) => z - v) ψ.target c₀.target := by
        intro z hz
        have : z - v ∈ (c₀.restrOpen S hS).target := hz.2
        exact this.1
      have h2 : ContMDiffOn (𝓡 1) (𝓡 1) ∞
          (fun z : EuclideanSpace ℝ (Fin 1) => c₀.symm (z - v)) ψ.target :=
        (contMDiffOn_symm_of_mem_maximalAtlas hc₀).comp
          ((contDiff_id.sub contDiff_const).contMDiff).contMDiffOn hmaps
      exact h2.congr fun z hz => rfl
  · intro y hy
    rw [hψs] at hy
    exact hy.2.1
  · intro y hy
    rw [hψs] at hy
    have hb : c₀ y ∈ Metric.ball a (1 / 2) := hy.2.2.2
    have h1 : |c₀ y 0 - a 0| < 1 / 2 := by
      have := (PiLp.norm_apply_le (c₀ y - a) 0).trans_lt (by simpa [dist_eq_norm] using hb)
      simpa using this
    have h2 : (ψ y) 0 = c₀ y 0 + (1 - a 0) := by
      rw [hψv]
      simp [v]
    rw [h2]
    linarith [(abs_lt.mp h1).1]

/-- **Adapted charts of a smooth domain.** Every point of `C` has a chart of the maximal atlas in
which `C` is the closed half-line `{ψ y 0 ≥ 0}`. -/
theorem exists_adaptedChart_EIM {C : Set Base}
    (hdom : ∀ c ∈ frontier C, ∃ U : TopologicalSpace.Opens Base, c ∈ U ∧ ∃ φ : Base → ℝ,
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
        C ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'})
    {x : Base} (hx : x ∈ C) :
    ∃ ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)),
      ψ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base ∧ x ∈ ψ.source ∧
        ∀ y ∈ ψ.source, (y ∈ C ↔ 0 ≤ ψ y 0) := by
  by_cases hint : x ∈ interior C
  · obtain ⟨ψ, hψ, hxψ, hsub, hpos⟩ := exists_chart_pos_EIM (isOpen_interior (s := C)) hint
    exact ⟨ψ, hψ, hxψ, fun y hy => ⟨fun _ => (hpos y hy).le, fun _ => interior_subset (hsub hy)⟩⟩
  · have hfr : x ∈ frontier C := ⟨subset_closure hx, hint⟩
    obtain ⟨U, hxU, φ, hφ, -, hd, heq⟩ := hdom x hfr
    obtain ⟨ψ, hψ, hxψ, hsub, hcoord⟩ := exists_chart_of_regular_EIM U.isOpen hφ hxU hd
    refine ⟨ψ, hψ, hxψ, fun y hy => ?_⟩
    rw [hcoord y hy]
    constructor
    · intro hyC
      have : y ∈ C ∩ (U : Set Base) := ⟨hyC, hsub hy⟩
      rw [heq] at this
      exact this.2
    · intro h0
      have : y ∈ {c' | c' ∈ U ∧ 0 ≤ φ c'} := ⟨hsub hy, h0⟩
      rw [← heq] at this
      exact this.1

end GC.GraphManifold.Assembly.FC39P0
