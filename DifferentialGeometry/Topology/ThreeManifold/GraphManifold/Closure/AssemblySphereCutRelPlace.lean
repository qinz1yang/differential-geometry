import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlaceBox
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutBallRelocation
import DifferentialGeometry.Topology.Manifold.AffineBallIsotopy
import DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension

/-!
# Chapter-14 assembly, relative COMPARE G2: placing a ball chart into a fibre tube

Lane ASM-L2e, group G2. In a connected manifold `M` (boundary allowed) with a tube chart `φ`
(radius-three solid torus in its source, target in the interior), a ball chart `c` of the interior
is carried, by a diffeomorphism `Ψ` of `M` fixed off a compact subset of the interior, onto the
fill `solidTubeFill φ` of a given ball chart `v` of the interior of the solid torus moved by a
diffeomorphism `Θ` of the solid torus which, near the boundary torus, is the identity or the
conjugation (`exists_solidPlacement`).

Proof. Both balls are relocated into the conjugation-symmetric box (`solidBox`, `tubeBox φ`) by the
interior-supported relocation of ASM-L2b (`exists_interiorIsotopy_image_subset_of_ballChart`), in
`M` and in the solid torus. In the box coordinates they are two embeddings `p₀, p₁` of the closed
radius-two ball into the convex box; composing `p₀` with the box reflection when the determinants
of the differentials at `0` have opposite signs (the conjugation `ε = true`), the Euclidean ball
isotopy `exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset` carries one onto the
other with compact support in the box; its transport to the solid torus by the box chart
(`exists_diffeomorph_extension_of_partial_chart_family`) completes `Θ`. No orientation of `M` is
used: the orientation choice is the sign of a determinant in one chart.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The scaling `x ↦ 2 x` of `E³`. -/
def scaleTwoE3 : E3 ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ E3 where
  toFun x := (2 : ℝ) • x
  invFun x := (1 / 2 : ℝ) • x
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]
  contMDiff_toFun := (contDiff_const_smul (2 : ℝ)).contMDiff
  contMDiff_invFun := (contDiff_const_smul (1 / 2 : ℝ)).contMDiff

section Scale

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A ball chart precomposed with the scaling by two. -/
def scaleTwoChart (c : PartialDiffeomorph 𝓘(ℝ, E3) I E3 M ∞) :
    PartialDiffeomorph 𝓘(ℝ, E3) I E3 M ∞ :=
  scaleTwoE3.toPartialDiffeomorph.trans c

theorem scaleTwoChart_source {c : PartialDiffeomorph 𝓘(ℝ, E3) I E3 M ∞}
    (hc : closedBall 0 2 ⊆ c.source) : closedBall (0 : E3) 1 ⊆ (scaleTwoChart c).source := by
  intro x hx
  refine ⟨mem_univ _, hc ?_⟩
  change (2 : ℝ) • x ∈ closedBall (0 : E3) 2
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have := mem_closedBall_zero_iff.mp hx
  linarith

theorem scaleTwoChart_target {c : PartialDiffeomorph 𝓘(ℝ, E3) I E3 M ∞} :
    (scaleTwoChart c).target ⊆ c.target := fun _ hy => hy.1

theorem scaleTwoChart_image (c : PartialDiffeomorph 𝓘(ℝ, E3) I E3 M ∞) :
    scaleTwoChart c '' closedBall 0 1 = c '' closedBall 0 2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(2 : ℝ) • x, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := mem_closedBall_zero_iff.mp hx
    linarith
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := mem_closedBall_zero_iff.mp hx
      linarith
    · change c ((2 : ℝ) • (1 / 2 : ℝ) • x) = c x
      rw [smul_smul]
      norm_num

end Scale

theorem differentiableAt_of_mem_source_pd
    (p : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) {x : E3} (hx : x ∈ p.source) :
    DifferentiableAt ℝ p x :=
  ((contMDiffOn_iff_contDiffOn.mp p.contMDiffOn_toFun).contDiffAt
    (p.open_source.mem_nhds hx)).differentiableAt (by simp)

/-- The differential of a partial diffeomorphism of `E³` at a source point has nonzero
determinant. -/
theorem det_fderiv_ne_zero_of_mem_source
    (p : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) {x : E3} (hx : x ∈ p.source) :
    (fderiv ℝ p x).det ≠ 0 := by
  have hd := differentiableAt_of_mem_source_pd p hx
  have hdi : DifferentiableAt ℝ p.symm (p x) :=
    differentiableAt_of_mem_source_pd p.symm (p.map_source hx)
  have heq : (p.symm ∘ p) =ᶠ[𝓝 x] id := by
    filter_upwards [p.open_source.mem_nhds hx] with y hy
    exact p.left_inv hy
  have hcomp : (fderiv ℝ p.symm (p x)).comp (fderiv ℝ p x) = ContinuousLinearMap.id ℝ E3 := by
    rw [← fderiv_comp x hdi hd, heq.fderiv_eq, fderiv_id]
  intro h0
  have hdet := congrArg (fun L : E3 →L[ℝ] E3 => LinearMap.det (L : E3 →ₗ[ℝ] E3)) hcomp
  change LinearMap.det (((fderiv ℝ p.symm (p x)) : E3 →ₗ[ℝ] E3).comp
    ((fderiv ℝ p x) : E3 →ₗ[ℝ] E3)) = LinearMap.det (LinearMap.id : E3 →ₗ[ℝ] E3) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  change _ * (fderiv ℝ p x).det = 1 at hdet
  rw [h0, mul_zero] at hdet
  exact zero_ne_one hdet

/-- **Sign choice.** Composing with the box reflection when needed, the two embeddings have
differentials at `0` with determinants of the same sign. -/
theorem exists_boxSign (p₀ p₁ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (h₀ : (0 : E3) ∈ p₀.source) (h₁ : (0 : E3) ∈ p₁.source) :
    ∃ ε : Bool, 0 < (fderiv ℝ (fun x => if ε then boxReflection (p₀ x) else p₀ x) 0).det *
      (fderiv ℝ p₁ 0).det := by
  have hd₀ := det_fderiv_ne_zero_of_mem_source p₀ h₀
  have hd₁ := det_fderiv_ne_zero_of_mem_source p₁ h₁
  by_cases hpos : 0 < (fderiv ℝ p₀ 0).det * (fderiv ℝ p₁ 0).det
  · exact ⟨false, by simpa using hpos⟩
  · refine ⟨true, ?_⟩
    have hR : fderiv ℝ (fun x => boxReflection (p₀ x)) 0 =
        (boxReflection : E3 →L[ℝ] E3).comp (fderiv ℝ p₀ 0) :=
      ((boxReflection : E3 →L[ℝ] E3).hasFDerivAt.comp 0
        (differentiableAt_of_mem_source_pd p₀ h₀).hasFDerivAt).fderiv
    have hdet : ((boxReflection : E3 →L[ℝ] E3).comp (fderiv ℝ p₀ 0)).det =
        -(fderiv ℝ p₀ 0).det := by
      change LinearMap.det (((boxReflection : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3).comp
        ((fderiv ℝ p₀ 0 : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3)) = _
      rw [LinearMap.det_comp]
      change LinearMap.det (boxReflection : E3 →ₗ[ℝ] E3) * _ = _
      rw [boxReflection_det]
      ring
    simp only [↓reduceIte]
    rw [hR, hdet]
    replace hpos := not_lt.mp hpos
    have hne : (fderiv ℝ p₀ 0).det * (fderiv ℝ p₁ 0).det ≠ 0 := mul_ne_zero hd₀ hd₁
    have hneg : (fderiv ℝ p₀ 0).det * (fderiv ℝ p₁ 0).det < 0 := lt_of_le_of_ne hpos hne
    linarith

/-- A uniform radius bound for a compact subset of the interior of the solid torus. -/
theorem exists_radius_lt_of_isCompact {K : Set solidSet.{u}} (hK : IsCompact K)
    (hKI : K ⊆ (𝓡∂ 3).interior solidSet.{u}) :
    ∃ R < (3 : ℝ), ∀ x ∈ K, ‖x.val.1.down‖ ≤ R := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨0, by norm_num, fun x hx => by rw [he] at hx; exact hx.elim⟩
  · have hc : ContinuousOn (fun x : solidSet.{u} => ‖x.val.1.down‖) K :=
      (continuous_norm.comp (continuous_uliftDown.comp
        (continuous_fst.comp continuous_subtype_val))).continuousOn
    obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne hc
    have hx₀I : (𝓡∂ 3).IsInteriorPoint x₀ := hKI hx₀
    rw [solidSet_isInteriorPoint_iff] at hx₀I
    exact ⟨‖x₀.val.1.down‖, hx₀I, fun x hx => hmax hx⟩

/-- The box reflection as a diffeomorphism. -/
def boxReflectionDiffeo : E3 ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ E3 where
  toEquiv := boxReflection.toEquiv
  contMDiff_toFun := boxReflection.contDiff.contMDiff
  contMDiff_invFun := boxReflection.symm.contDiff.contMDiff

/-- **G2 (ASM-L2e): placement of a ball chart into a fibre tube.** -/
theorem exists_solidPlacement {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [ConnectedSpace M]
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (hφI : φ.target ⊆ I.interior M)
    (c : PartialDiffeomorph (𝓡 3) I E3 M ∞) (hc : closedBall 0 2 ⊆ c.source)
    (hcI : c.target ⊆ I.interior M)
    (v : PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞) (hv : closedBall 0 2 ⊆ v.source)
    (hvI : v.target ⊆ (𝓡∂ 3).interior solidSet.{u}) :
    ∃ (ε : Bool) (Ψ : M ≃ₘ⟮I, I⟯ M) (Θ : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u})
      (K : Set M) (r : ℝ),
      IsCompact K ∧ K ⊆ I.interior M ∧ (∀ x, x ∉ K → Ψ x = x) ∧ r < 3 ∧
      (∀ x : solidSet.{u}, r ≤ ‖x.val.1.down‖ → (Θ x).val =
        if ε then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val) ∧
      ∀ x ∈ closedBall (0 : E3) 2, Ψ (c x) = solidTubeFill φ (Θ (v x)) := by
  -- the box is nonempty in both manifolds
  obtain ⟨x₀, hx₀⟩ := boxSet_nonempty
  have hx₀S : x₀ ∈ solidBox.{u}.source := by rw [solidBox_source]; exact hx₀
  have hx₀M : x₀ ∈ (tubeBox φ).source := by rw [tubeBox_source φ h3]; exact hx₀
  have hbS : (solidBox.{u}.target ∩ (𝓡∂ 3).interior solidSet.{u}).Nonempty :=
    ⟨solidBox x₀, solidBox.map_source hx₀S, solidBox_target_interior (solidBox.map_source hx₀S)⟩
  have hbM : ((tubeBox φ).target ∩ I.interior M).Nonempty :=
    ⟨tubeBox φ x₀, (tubeBox φ).map_source hx₀M,
      hφI (tubeBox_target_subset φ ((tubeBox φ).map_source hx₀M))⟩
  -- relocation of the solid ball and of the ball of `M` into the box
  obtain ⟨ΨS, -, -, ⟨KS, hKS, hKSI, hKSfix⟩, hΛ⟩ :=
    exists_interiorIsotopy_image_subset_of_ballChart (scaleTwoChart v) (scaleTwoChart_source hv)
      (fun y hy => hvI (scaleTwoChart_target hy)) solidBox.open_target hbS
  rw [scaleTwoChart_image] at hΛ
  obtain ⟨ΨM, -, -, ⟨KM, hKM, hKMI, hKMfix⟩, hΨ⟩ :=
    exists_interiorIsotopy_image_subset_of_ballChart (scaleTwoChart c) (scaleTwoChart_source hc)
      (fun y hy => hcI (scaleTwoChart_target hy)) (tubeBox φ).open_target hbM
  rw [scaleTwoChart_image] at hΨ
  -- the two embeddings in the box coordinates
  let p₀ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    (v.trans (ΨS 1).toPartialDiffeomorph).trans solidBox.symm
  let p₁ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    (c.trans (ΨM 1).toPartialDiffeomorph).trans (tubeBox φ).symm
  have hp₀ : ∀ x ∈ closedBall (0 : E3) 2,
      x ∈ p₀.source ∧ solidBox (p₀ x) = ΨS 1 (v x) ∧ p₀ x ∈ boxSet := by
    intro x hx
    have hT : ΨS 1 (v x) ∈ solidBox.{u}.target := hΛ ⟨v x, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨⟨hv hx, mem_univ _⟩, hT⟩, solidBox.right_inv hT, ?_⟩
    rw [← solidBox_source]
    exact solidBox.map_target hT
  have hp₁ : ∀ x ∈ closedBall (0 : E3) 2,
      x ∈ p₁.source ∧ tubeBox φ (p₁ x) = ΨM 1 (c x) ∧ p₁ x ∈ boxSet := by
    intro x hx
    have hT : ΨM 1 (c x) ∈ (tubeBox φ).target := hΨ ⟨c x, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨⟨hc hx, mem_univ _⟩, hT⟩, (tubeBox φ).right_inv hT, ?_⟩
    rw [← tubeBox_source φ h3]
    exact (tubeBox φ).map_target hT
  have h0 : (0 : E3) ∈ closedBall (0 : E3) 2 := mem_closedBall_self (by norm_num)
  obtain ⟨ε, hε⟩ := exists_boxSign p₀ p₁ (hp₀ 0 h0).1 (hp₁ 0 h0).1
  -- the reflected first embedding
  let q₀ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    if ε then p₀.trans boxReflectionDiffeo.toPartialDiffeomorph else p₀
  have hq₀ : ⇑q₀ = fun x => if ε then boxReflection (p₀ x) else p₀ x := by
    cases ε <;> rfl
  have hq₀s : closedBall (0 : E3) 2 ⊆ q₀.source := by
    intro x hx
    cases ε
    · exact (hp₀ x hx).1
    · exact ⟨(hp₀ x hx).1, mem_univ _⟩
  have hq₀V : ∀ x ∈ closedBall (0 : E3) 2, q₀ x ∈ boxSet := by
    intro x hx
    rw [hq₀]
    cases ε
    · exact (hp₀ x hx).2.2
    · exact boxReflection_mem (hp₀ x hx).2.2
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • q₀ 0 + t • p₁ 0 ∈ boxSet := by
    intro t ht
    exact convex_boxSet (hq₀V 0 h0) (hp₁ 0 h0).2.2 (by linarith [ht.2]) ht.1 (by ring)
  have hori : 0 < (fderiv ℝ (q₀ : E3 → E3) 0).det * (fderiv ℝ (p₁ : E3 → E3) 0).det := by
    rw [hq₀]
    exact hε
  obtain ⟨J, hJc, hJic, -, hJ1, KJ, hKJ, hKJV, hKJfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset
      q₀ p₁ hq₀s (fun x hx => (hp₁ x hx).1) isOpen_boxSet
      (by rintro _ ⟨x, hx, rfl⟩; exact hq₀V x hx) (by rintro _ ⟨x, hx, rfl⟩; exact (hp₁ x hx).2.2)
      hseg hori
  -- transport of the Euclidean isotopy into the solid torus
  have hKJt : KJ ⊆ (solidBox.{u}).symm.toOpenPartialHomeomorph.target := by
    intro z hz
    change z ∈ solidBox.{u}.source
    rw [solidBox_source]
    exact hKJV hz
  obtain ⟨Ĵ, -, -, hĴ, -, -, hĴfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_partial_chart_family
      (solidBox.{u}).symm.toOpenPartialHomeomorph solidBox.contMDiffOn_invFun
      solidBox.contMDiffOn_toFun J hJc hJic hKJ hKJt hKJfix
  have hĴbox : ∀ z ∈ boxSet, Ĵ 1 (solidBox.{u} z) = solidBox.{u} (J 1 z) := by
    intro z hz
    have hzS : z ∈ solidBox.{u}.source := by rw [solidBox_source]; exact hz
    rw [(hĴ 1 (solidBox z)).1, DifferentialGeometry.Topology.Manifold.extendChartById]
    split_ifs with hmem
    · exact congrArg (fun w => solidBox.{u} (J 1 w)) (solidBox.left_inv hzS)
    · exact (hmem (solidBox.map_source hzS)).elim
  -- the radius bound
  obtain ⟨R0, hR0, hR0K⟩ := exists_radius_lt_of_isCompact hKS hKSI
  let r : ℝ := (max R0 (1 / 4) + 3) / 2
  have hr3 : r < 3 := by
    have : max R0 (1 / 4) < 3 := max_lt hR0 (by norm_num)
    change (max R0 (1 / 4) + 3) / 2 < 3
    linarith
  have hrR0 : R0 < r := by
    have : R0 ≤ max R0 (1 / 4) := le_max_left _ _
    have : max R0 (1 / 4) < 3 := max_lt hR0 (by norm_num)
    change R0 < (max R0 (1 / 4) + 3) / 2
    linarith
  have hr4 : (1 / 4 : ℝ) < r := by
    have : (1 / 4 : ℝ) ≤ max R0 (1 / 4) := le_max_right _ _
    change (1 / 4 : ℝ) < (max R0 (1 / 4) + 3) / 2
    linarith
  refine ⟨ε, ΨM 1, (ΨS 1).trans ((solidConj ε).trans (Ĵ 1)), KM, r, hKM, hKMI,
    fun x hx => hKMfix 1 x hx, hr3, ?_, ?_⟩
  · intro x hx
    have hxK : x ∉ KS := fun h => by linarith [hR0K x h]
    have hΛx : ΨS 1 x = x := hKSfix 1 x hxK
    have hfix : solidConj ε x ∉ solidBox.{u} '' KJ := by
      rintro ⟨z, hz, hze⟩
      have hzS : z ∈ solidBox.{u}.source := by rw [solidBox_source]; exact hKJV hz
      have hlt := solidBox_target_norm (hze ▸ solidBox.map_source hzS)
      rw [solidConj_norm] at hlt
      linarith
    change (Ĵ 1 (solidConj ε (ΨS 1 x))).val = _
    rw [hΛx, (hĴfix 1 _ hfix).1, solidConj_val]
  · intro x hx
    obtain ⟨-, hp₀b, hp₀V⟩ := hp₀ x hx
    obtain ⟨-, hp₁b, hp₁V⟩ := hp₁ x hx
    change ΨM 1 (c x) = solidTubeFill φ (Ĵ 1 (solidConj ε (ΨS 1 (v x))))
    rw [← hp₀b, solidConj_solidBox ε hp₀V]
    have hq : (if ε then boxReflection (p₀ x) else p₀ x) = q₀ x := by rw [hq₀]
    rw [hq, hĴbox _ (hq₀V x hx), hJ1 x hx, solidTubeFill_solidBox φ hp₁V, hp₁b]

end GC.GraphManifold.Assembly
