import DifferentialGeometry.Topology.Manifold.RegularLevel.BoundarySublevel
import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX

/-!
# Half-space slice manifolds in an ambient WITH boundary: the inclusion is a smooth embedding

Lane O-CROSS (G1/G2). Companion of `HalfSpaceSliceImmersion.lean` (ambient self model) for an
ambient manifold `M` modelled on `𝓡∂ (d + 1)` and slice charts
`Φ : M ⊇ U ≅ V ⊆ H^{d+1} × ℝ⁰` of height `c` (`P y ↔ (Φ y).2 = 0 ∧ c ≤ (Φ y)₁₀`):

* `slice_chart_written_OCX`: in the slice chart of `{x // P x}` the inclusion reads
  `u ↦ u + c e₀` in the ambient coordinates `(Φ ·)₁`;
* `slice_isImmersionAtOfComplement_val_bdry_OCX`: at height `c = 0` the code chart is
  `Φ` followed by `H × ℝ⁰ ≅ H` (normal form the identity); at height `c > 0` the point lies in the
  open half-space of `Φ` and the vector-chart kernel
  `isImmersionAtOfComplement_halfSpace_of_affine_OCX`
  (recentring along a boundary direction `s₀`, Householder reflection) applies;
* `boundarySublevel_isSmoothEmbedding_val_OCX`: for a regular sublevel `{f ≤ r}` of a manifold with
  boundary (lane SUB-BDY's `boundarySublevelChartedSpace`, dimension at least two) the inclusion
  is a smooth embedding `𝓡∂ → 𝓡∂`.
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.RegularLevel

/-- `H × ℝ⁰ ≅ H`. -/
def halfSpaceProdFinZero_OCX (d : ℕ) :
    Diffeomorph ((𝓡∂ (d + 1)).prod 𝓘(ℝ, Fin 0 → ℝ)) (𝓡∂ (d + 1))
      (EuclideanHalfSpace (d + 1) × (Fin 0 → ℝ)) (EuclideanHalfSpace (d + 1)) ∞ where
  toFun q := q.1
  invFun h := (h, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_fst
  contMDiff_invFun := contMDiff_id.prodMk contMDiff_const

section Written

variable {d : ℕ} {E' H' M F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The inclusion in a slice chart**: for `u` in the extended target of the slice chart of
height `c`, the point `φ⁻¹ u` lies in `Φ.source` and `Φ (φ⁻¹ u) = (u + c e₀, 0)`. -/
theorem slice_chart_written_OCX (P : M → Prop)
    (Φ : PartialDiffeomorph I ((𝓡∂ (d + 1)).prod 𝓘(ℝ, F)) M (EuclideanHalfSpace (d + 1) × F) ∞)
    {c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ y ∈ Φ.source, P y ↔ ((Φ y).2 = 0 ∧ c ≤ (Φ y).1.1 0))
    (x₀ : {x // P x}) {u : EuclideanSpace ℝ (Fin (d + 1))}
    (hu : u ∈ ((sliceChart P Φ hc hΦ x₀).extend (𝓡∂ (d + 1))).target) :
    (((sliceChart P Φ hc hΦ x₀).extend (𝓡∂ (d + 1))).symm u).1 ∈ Φ.source ∧
      (Φ (((sliceChart P Φ hc hΦ x₀).extend (𝓡∂ (d + 1))).symm u).1).1.1 =
        u + c • EuclideanSpace.single 0 1 ∧
      (Φ (((sliceChart P Φ hc hΦ x₀).extend (𝓡∂ (d + 1))).symm u).1).2 = 0 := by
  obtain ⟨hy2, hy1⟩ := hu
  set w : EuclideanHalfSpace (d + 1) := (𝓡∂ (d + 1)).symm u with hwdef
  have hw : (sliceShift d c w, (0 : F)) ∈ Φ.target := hy1
  have hwy : w.1 = u := (𝓡∂ (d + 1)).right_inv (by rwa [← ModelWithCorners.target_eq])
  have hinv : (((sliceChart P Φ hc hΦ x₀).extend (𝓡∂ (d + 1))).symm u : M) =
      Φ.symm (sliceShift d c w, 0) := by
    rw [OpenPartialHomeomorph.extend_coe_symm]
    exact sliceChartInv_val P Φ hc hΦ x₀ hw
  have hr : Φ (Φ.symm (sliceShift d c w, (0 : F))) = (sliceShift d c w, 0) := Φ.right_inv hw
  rw [hinv, hr]
  refine ⟨Φ.map_target hw, ?_, rfl⟩
  change (sliceShift d c w).1 = u + c • EuclideanSpace.single 0 1
  rw [sliceShift_val hc w, hwy]

end Written

section Immersion

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (d + 1)) M]
  [IsManifold (𝓡∂ (d + 1)) ∞ M]
  (P Bd : M → Prop)
  (hP : ∀ x, P x → ∃ p : PartialDiffeomorph (𝓡∂ (d + 1)) ((𝓡∂ (d + 1)).prod 𝓘(ℝ, Fin 0 → ℝ)) M
        (EuclideanHalfSpace (d + 1) × (Fin 0 → ℝ)) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, P y ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ Bd x))

/-- **The slice inclusion into an ambient with boundary is an immersion at every point**, given a
boundary direction `s₀` of the model (`s₀ ≠ 0`, `s₀ 0 = 0`; dimension at least two). -/
theorem slice_isImmersionAtOfComplement_val_bdry_OCX (s₀ : EuclideanSpace ℝ (Fin (d + 1)))
    (hs₀ : s₀ ≠ 0) (hs₀0 : s₀ 0 = 0) (x : {x // P x}) :
    letI := sliceChartedSpace P Bd hP
    IsImmersionAtOfComplement (Fin 0 → ℝ) (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞
      (Subtype.val : {x // P x} → M) x := by
  let _ := sliceChartedSpace P Bd hP
  have _ : IsManifold (𝓡∂ (d + 1)) ∞ {x // P x} := slice_isManifold P Bd hP
  obtain ⟨hc, hx, hΦ, -⟩ := (hP x.1 x.2).choose_spec
  have hφmem : sliceChart P (hP x.1 x.2).choose.1 hc hΦ x ∈
      IsManifold.maximalAtlas (𝓡∂ (d + 1)) ∞ {x // P x} :=
    IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (d + 1)) x
  have hxsrc : x ∈ (sliceChart P (hP x.1 x.2).choose.1 hc hΦ x).source := hx
  let L := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin (d + 1))) (Fin 0 → ℝ)
  by_cases hc0 : (hP x.1 x.2).choose.2 = 0
  · let ψ := (hP x.1 x.2).choose.1.trans (halfSpaceProdFinZero_OCX d).toPartialDiffeomorph
    apply IsImmersionAtOfComplement.mk_of_charts L (sliceChart P (hP x.1 x.2).choose.1 hc hΦ x)
      ψ.toOpenPartialHomeomorph hxsrc ⟨hx, mem_univ _⟩ hφmem ψ.mem_maximalAtlas_OCX
      (fun y hy => ⟨hy, mem_univ _⟩)
    intro u hu
    obtain ⟨-, h1, -⟩ := slice_chart_written_OCX P (hP x.1 x.2).choose.1 hc hΦ x hu
    change ((hP x.1 x.2).choose.1
      (((sliceChart P (hP x.1 x.2).choose.1 hc hΦ x).extend (𝓡∂ (d + 1))).symm u).1).1.1 =
      L (u, 0)
    rw [h1, hc0, zero_smul, add_zero]
    rfl
  · have hcpos : 0 < (hP x.1 x.2).choose.2 := lt_of_le_of_ne hc (Ne.symm hc0)
    let β := (hP x.1 x.2).choose.1.trans ((sliceHalfSpaceProd (d := d) (Fin 0 → ℝ)).symm.trans
      (affineDiffeomorph_OCX L 0).toPartialDiffeomorph)
    have hs₀I : ∀ v, v + s₀ ∈ range (𝓡∂ (d + 1)) ↔ v ∈ range (𝓡∂ (d + 1)) := by
      intro v
      rw [range_modelWithCornersEuclideanHalfSpace]
      simp [hs₀0]
    refine isImmersionAtOfComplement_halfSpace_of_affine_OCX s₀ hs₀ hs₀I
      (sliceChart P (hP x.1 x.2).choose.1 hc hΦ x) hφmem hxsrc β ?_ L
      ((hP x.1 x.2).choose.2 • EuclideanSpace.single 0 1) ?_
    · intro y hy
      have hP' := (hΦ y.1 hy).mp y.2
      exact ⟨hy, lt_of_lt_of_le hcpos hP'.2, mem_univ _⟩
    · intro u hu
      obtain ⟨-, h1, h2⟩ := slice_chart_written_OCX P (hP x.1 x.2).choose.1 hc hΦ x hu
      change L (((hP x.1 x.2).choose.1
        (((sliceChart P (hP x.1 x.2).choose.1 hc hΦ x).extend (𝓡∂ (d + 1))).symm u).1).1.1,
        ((hP x.1 x.2).choose.1
        (((sliceChart P (hP x.1 x.2).choose.1 hc hΦ x).extend (𝓡∂ (d + 1))).symm u).1).2) + 0 =
        L (u, 0) + (hP x.1 x.2).choose.2 • EuclideanSpace.single 0 1
      rw [h1, add_zero]
      rfl

/-- Global form: the slice inclusion is an immersion with complement `ℝ⁰`. -/
theorem slice_isImmersionOfComplement_val_bdry_OCX (s₀ : EuclideanSpace ℝ (Fin (d + 1)))
    (hs₀ : s₀ ≠ 0) (hs₀0 : s₀ 0 = 0) :
    letI := sliceChartedSpace P Bd hP
    IsImmersionOfComplement (Fin 0 → ℝ) (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞
      (Subtype.val : {x // P x} → M) :=
  fun x => slice_isImmersionAtOfComplement_val_bdry_OCX P Bd hP s₀ hs₀ hs₀0 x

/-- **The slice inclusion is a smooth embedding** (ambient with boundary). -/
theorem slice_isSmoothEmbedding_val_bdry_OCX (s₀ : EuclideanSpace ℝ (Fin (d + 1)))
    (hs₀ : s₀ ≠ 0) (hs₀0 : s₀ 0 = 0) :
    letI := sliceChartedSpace P Bd hP
    IsSmoothEmbedding (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞ (Subtype.val : {x // P x} → M) := by
  let _ := sliceChartedSpace P Bd hP
  exact ⟨(slice_isImmersionOfComplement_val_bdry_OCX P Bd hP s₀ hs₀ hs₀0).isImmersion,
    Topology.IsEmbedding.subtypeVal⟩

end Immersion

end DifferentialGeometry.Manifold.RegularLevel

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1 + 1)) M] [IsManifold (𝓡∂ (m + 1 + 1)) ∞ M]

/-- **A regular sublevel of a manifold with boundary is a smooth submanifold with boundary**: the
inclusion `{f ≤ r} → M` is a smooth embedding `𝓡∂ (m + 2) → 𝓡∂ (m + 2)` (lane SUB-BDY's charted
space; the regular level lies in the interior). -/
theorem boundarySublevel_isSmoothEmbedding_val_OCX (f : M → ℝ) (r : ℝ)
    (hf : ContMDiff (𝓡∂ (m + 1 + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = r → mfderiv (𝓡∂ (m + 1 + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hint : ∀ x : M, f x = r → (𝓡∂ (m + 1 + 1)).IsInteriorPoint x) :
    letI := boundarySublevelChartedSpace f r hf hreg hint
    IsSmoothEmbedding (𝓡∂ (m + 1 + 1)) (𝓡∂ (m + 1 + 1)) ∞
      (fun x : {x : M // f x ≤ r} => x.1) := by
  have hs₀ : (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin (m + 1 + 1))) ≠ 0 := by
    intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1 + 1)) => v 1) h
    simp at h1
  have hs₀0 : (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin (m + 1 + 1))) 0 = 0 := by
    simp
  exact slice_isSmoothEmbedding_val_bdry_OCX _ _ (boundarySublevel_sliceCharts f r hf hreg hint)
    _ hs₀ hs₀0

end DifferentialGeometry.Topology.Manifold
