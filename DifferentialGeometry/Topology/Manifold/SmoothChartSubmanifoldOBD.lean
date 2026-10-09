import DifferentialGeometry.Topology.Manifold.LocalSliceManifold

/-!
# Embedded submanifolds in AFFINE chart form (lane S-BD2, suffix `_OBD`)

The charts of `LinearChartSubmanifold` (lane C14-REG-CHAIN) with a SMOOTH chart map
`κ i : H → E` in place of a continuous linear one (an affine map `L y - c` is the case needed for
the stage bases of the boundary landing: the chart is centred at `κ y₀ = 0`, which a linear `κ`
cannot do in general). Same statements and proofs: `linearChart_OBD` (chart of the subtype),
`linearChartedSpace_OBD`, `linearIsManifold_OBD`, `contMDiff_linearInclusion_OBD`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **The linear chart of a subset in chart form**: on the piece `W ∩ O`, the continuous linear
map `κ` is a bijection onto `B(0, r)` with continuous inverse `φ`; `y₀` is a default point. -/
def linearChart_OBD (W : Set H) (κ : H → E) (hκs : ContDiff ℝ ∞ κ) (φ : E → H) (O : Set H) (r : ℝ)
    (hO : IsOpen O) (hφc : ContinuousOn φ (ball 0 r))
    (hφ : ∀ b ∈ ball (0 : E) r, φ b ∈ W ∩ O ∧ κ (φ b) = b)
    (hκ : ∀ y ∈ W ∩ O, κ y ∈ ball (0 : E) r ∧ φ (κ y) = y) (y₀ : W) :
    OpenPartialHomeomorph W E := by
  classical
  let inv : E → W := fun b => if hb : b ∈ ball (0 : E) r then ⟨φ b, (hφ b hb).1.1⟩ else y₀
  refine
    { toFun := fun y => κ y.1
      invFun := inv
      source := Subtype.val ⁻¹' O
      target := ball (0 : E) r
      map_source' := fun y hy => (hκ y.1 ⟨y.2, hy⟩).1
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := hO.preimage continuous_subtype_val
      open_target := isOpen_ball
      continuousOn_toFun := (hκs.continuous.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := ?_ }
  · intro b hb
    change (inv b).1 ∈ O
    simp only [inv, dite_eq_left hb]
    exact (hφ b hb).1.2
  · intro y hy
    have h := hκ y.1 ⟨y.2, hy⟩
    apply Subtype.ext
    simp only [inv, dite_eq_left h.1]
    exact h.2
  · intro b hb
    simp only [inv, dite_eq_left hb]
    exact (hφ b hb).2
  · rw [continuousOn_iff_continuous_domRestrict]
    apply Continuous.subtype_mk
    have hc : Continuous (fun z : ball (0 : E) r => φ z.1) := by
      apply continuousOn_univ.mp
      exact hφc.comp continuous_subtype_val.continuousOn (fun z _ => z.2)
    apply hc.congr
    intro z
    have hv : inv z.1 = ⟨φ z.1, (hφ z.1 z.2).1.1⟩ := dite_eq_left z.2
    exact (congrArg Subtype.val hv).symm

section Chart

variable (W : Set H) (κ : H → E) (hκs : ContDiff ℝ ∞ κ) (φ : E → H) (O : Set H) (r : ℝ)
    (hO : IsOpen O)
  (hφc : ContinuousOn φ (ball 0 r)) (hφ : ∀ b ∈ ball (0 : E) r, φ b ∈ W ∩ O ∧ κ (φ b) = b)
  (hκ : ∀ y ∈ W ∩ O, κ y ∈ ball (0 : E) r ∧ φ (κ y) = y) (y₀ : W)

/-- The linear chart is `κ`. -/
theorem linearChart_OBD_apply (y : W) :
    linearChart_OBD W κ hκs φ O r hO hφc hφ hκ y₀ y = κ y.1 :=
  rfl

/-- The inverse of the linear chart is `φ` on the ball. -/
theorem linearChart_OBD_symm_val {b : E} (hb : b ∈ ball (0 : E) r) :
    ((linearChart_OBD W κ hκs φ O r hO hφc hφ hκ y₀).symm b : H) = φ b := by
  classical
  change ((if hb : b ∈ ball (0 : E) r then (⟨φ b, (hφ b hb).1.1⟩ : W) else y₀) : W).1 = φ b
  rw [dite_eq_left hb]

end Chart

variable {ι : Type*}

/-- The covering piece chosen at a point of `W`. -/
def linearChartIdx_OBD (W : Set H) (O : ι → Set H) (hcov : W ⊆ ⋃ i, O i) (y : W) : ι :=
  Classical.choose (mem_iUnion.mp (hcov y.2))

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem mem_linearChartIdx_OBD (W : Set H) (O : ι → Set H) (hcov : W ⊆ ⋃ i, O i) (y : W) :
    y.1 ∈ O (linearChartIdx_OBD W O hcov y) :=
  Classical.choose_spec (mem_iUnion.mp (hcov y.2))

/-- The chart of `W` at `y`: the linear chart of the covering piece chosen at `y`. -/
def linearChartAt_OBD (W : Set H) (κ : ι → H → E) (hκs : ∀ i, ContDiff ℝ ∞ (κ i))
    (φ : ι → E → H) (O : ι → Set H)
    (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (y : W) : OpenPartialHomeomorph W E :=
  linearChart_OBD W (κ (linearChartIdx_OBD W O hcov y))
    (hκs (linearChartIdx_OBD W O hcov y)) (φ (linearChartIdx_OBD W O hcov y))
    (O (linearChartIdx_OBD W O hcov y)) r (hO _) (hφs _).continuousOn (hφ _) (hκ _) y

/-- The inverse of the chart at `y` is the parametrization of the chosen piece on the ball. -/
theorem linearChartAt_OBD_symm_val (W : Set H) (κ : ι → H → E) (hκs : ∀ i, ContDiff ℝ ∞ (κ i))
    (φ : ι → E → H)
    (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (y : W) {b : E} (hb : b ∈ ball (0 : E) r) :
    ((linearChartAt_OBD W κ hκs φ O r hO hφs hφ hκ hcov y).symm b : H) =
      φ (linearChartIdx_OBD W O hcov y) b :=
  linearChart_OBD_symm_val _ _ _ _ _ _ _ _ _ _ _ hb

/-- **The charted space of a subset in chart form** (model `E`). -/
@[reducible]
def linearChartedSpace_OBD (W : Set H) (κ : ι → H → E) (hκs : ∀ i, ContDiff ℝ ∞ (κ i))
    (φ : ι → E → H) (O : ι → Set H)
    (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) : ChartedSpace E W where
  atlas := range (linearChartAt_OBD W κ hκs φ O r hO hφs hφ hκ hcov)
  chartAt := linearChartAt_OBD W κ hκs φ O r hO hφs hφ hκ hcov
  mem_chart_source y := mem_linearChartIdx_OBD W O hcov y
  chart_mem_atlas y := ⟨y, rfl⟩

/-- **A subset in chart form is a smooth manifold** (transition maps `κ i' ∘ φ i`). -/
theorem linearIsManifold_OBD (W : Set H) (κ : ι → H → E) (hκs : ∀ i, ContDiff ℝ ∞ (κ i))
    (φ : ι → E → H) (O : ι → Set H)
    (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) :
    let _ := linearChartedSpace_OBD W κ hκs φ O r hO hφs hφ hκ hcov
    IsManifold 𝓘(ℝ, E) ∞ W := by
  dsimp only
  let _ := linearChartedSpace_OBD W κ hκs φ O r hO hφs hφ hκ hcov
  refine { toHasGroupoid := ?_ }
  apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ∞ 𝓘(ℝ, E))
  rintro c c' ⟨x, rfl⟩ ⟨y, rfl⟩
  change ContDiffOn ℝ ∞ (𝓘(ℝ, E) ∘ _ ∘ (𝓘(ℝ, E)).symm) _
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  refine ((hκs (linearChartIdx_OBD W O hcov y)).comp_contDiffOn
    ((hφs (linearChartIdx_OBD W O hcov x)).mono fun b hb => hb.1)).congr fun b hb => ?_
  exact congrArg (κ (linearChartIdx_OBD W O hcov y))
    (linearChartAt_OBD_symm_val W κ hκs φ O r hO hφs hφ hκ hcov x hb.1)

/-- **The inclusion of a subset in chart form is smooth.** -/
theorem contMDiff_linearInclusion_OBD (W : Set H) (κ : ι → H → E) (hκs : ∀ i, ContDiff ℝ ∞
    (κ i)) (φ : ι → E → H)
    (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) :
    let _ := linearChartedSpace_OBD W κ hκs φ O r hO hφs hφ hκ hcov
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (Subtype.val : W → H) := by
  dsimp only
  let _ := linearChartedSpace_OBD W κ hκs φ O r hO hφs hφ hκ hcov
  intro x
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, H) ∞
    (Subtype.val ∘ (linearChartAt_OBD W κ hκs φ O r hO hφs hφ hκ hcov x).symm)
    ((linearChartAt_OBD W κ hκs φ O r hO hφs hφ hκ hcov x) x)
  have hc : ContDiffOn ℝ ∞
      (Subtype.val ∘ (linearChartAt_OBD W κ hκs φ O r hO hφs hφ hκ hcov x).symm) (ball 0 r) :=
    (hφs (linearChartIdx_OBD W O hcov x)).congr fun b hb =>
      linearChartAt_OBD_symm_val W κ hκs φ O r hO hφs hφ hκ hcov x hb
  exact hc.contMDiffOn.contMDiffAt (isOpen_ball.mem_nhds
    ((linearChartAt_OBD W κ hκs φ O r hO hφs hφ hκ hcov x).map_source (mem_chart_source E x)))

/-- **The inclusion of a subset in chart form has injective differential** (an immersion). -/
theorem mfderiv_linearInclusion_injective_OBD (W : Set H) (κ : ι → H → E)
    (hκs : ∀ i, ContDiff ℝ ∞ (κ i))
    (φ : ι → E → H) (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i))
    (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (x : W) :
    let _ := linearChartedSpace_OBD W κ hκs φ O r hO hφs hφ hκ hcov
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : W → H) x) := by
  dsimp only
  let _ := linearChartedSpace_OBD W κ hκs φ O r hO hφs hφ hκ hcov
  let _ : IsManifold 𝓘(ℝ, E) ∞ W := linearIsManifold_OBD W κ hκs φ O r hO hφs hφ hκ hcov
  let c := chartAt E x
  have hcd : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp)⟩
  have hci := hcd.mfderiv_injective (mem_chart_source E x)
  let gk : H → E := κ (linearChartIdx_OBD W O hcov x)
  have hgd : MDifferentiableAt 𝓘(ℝ, H) 𝓘(ℝ, E) gk (x : H) :=
    (((hκs (linearChartIdx_OBD W O hcov x)).differentiable (by simp)) (x : H)).mdifferentiableAt
  have hid := ((contMDiff_linearInclusion_OBD W κ hκs φ O r hO hφs hφ hκ hcov) x).mdifferentiableAt
    (by simp)
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c x =
      (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) gk (x : H)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : W → H) x) :=
    mfderiv_comp x hgd hid
  intro u v huv
  apply hci
  rw [hd]
  exact congrArg (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) gk (x : H)) huv


end DifferentialGeometry.Topology.Manifold
