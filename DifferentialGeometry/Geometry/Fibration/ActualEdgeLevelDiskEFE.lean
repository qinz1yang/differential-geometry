import DifferentialGeometry.Geometry.Fibration.ActualEdgeDiskCoverageApplications
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBufferCollarApplications
import DifferentialGeometry.Topology.Ehresmann.WholeDiskTransport
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacketSmoothEFE

/-!
# EDP04, original whole disks at every level `|a| < 4Δ` as smooth embeddings (chart level)

Lane S-EDP-FDC, group G3 (EDP04 whole-disk binding, steps A and B). Blueprint `master207B.tex`,
EDP04 (B:6949–7038), draft 74 D74-11 ("`fibre_disk` by EDP04's whole-trace isotopy to the original
disk, output: smooth embedding"). On the actual edge chart `j` of `L : LocalChartPacketsC14`, with
`η = η_j`, `H₀ = edgeRowHeight Δ F ρ` and the original source
`Y_j = {p ∈ B(j, 100Δρ(j)) : |η| < 5Δ, t < 5Δ}`:

* `LocalChartPacketsC14.edge_smoothDisk_EFE` (step A): the ORIGINAL LFR28 disk (the packet's
  `diskModel`, `EdgeDiskPacketSmoothEFE`) is a smooth embedding `ClosedCell 2 → X` onto the whole
  zero fibre `{η_j = 0, H₀ ≤ 4Δ}` of `B(j, 100Δρ(j))`, boundary circle onto the rim `{H₀ = 4Δ}`;
* `LocalChartPacketsC14.edge_levelDisk_EFE` (step B): the same at every level `|a| < 4Δ`:
  E0 (`wholeDisk_of_compact_transverse_trace_opens_EFC`) applied to the family `(η_j - τ a, H₀)`,
  `τ ∈ [0, 1]`, whose whole trace lies in EDP03's compact buffer (`edp03_buffer`) and which is
  transverse to `{h = 0}` (EDP03: `dη_j > .99`) and has rank two on its rim (the collar co-norm of
  the ORIGINAL pair, `EdgeFamily.collar_height_conorm_EDP3`);
* calculus helpers for the pair `(f, h)` of real functions (`mvfderiv_pair_apply_EFE`,
  `surjective_mfderiv_pair_EFE`, `pair_form_of_surjective_edgeReference_EFE`,
  `mvfderiv_sub_const_EFE`, `surjective_mfderiv_of_mvfderiv_ne_zero_EFE`,
  `mvfderiv_homotopy_scalar_EFE`) and the openness of `Y_j` (`isOpen_edgeSource_EFE`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A real function with a nonzero directional derivative at `x` is a submersion there. -/
theorem surjective_mfderiv_of_mvfderiv_ne_zero_EFE {f : M → ℝ} {x : M}
    (w : TangentSpace I x) (hw : mvfderiv (I := I) f x w ≠ 0) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ) f x) := by
  intro y'
  let y : ℝ := y'
  refine ⟨(y / mvfderiv (I := I) f x w) • w, ?_⟩
  change mvfderiv (I := I) f x ((y / mvfderiv (I := I) f x w) • w) = y
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ y hw

/-- The differential of a pair of real functions, in the pair form. -/
theorem mvfderiv_pair_apply_EFE {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x)
    (W : TangentSpace I x) :
    mvfderiv (I := I) (fun z => (f z, h z)) x W =
      (mvfderiv (I := I) f x W, mvfderiv (I := I) h x W) := by
  let ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))
  have hGc : ∀ k, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (![f, h] k) x := fun k => by
    fin_cases k
    · exact hf
    · exact hh
  have hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (edgeReferenceCoordinates ![f, h]) x :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin 2 => ℝ)).symm.differentiableAt.mdifferentiableAt
      |>.comp x (((contMDiffAt_pi_space).2 hGc).mdifferentiableAt (by simp)))
  have hfun : (fun z => (f z, h z)) = fun z => ℓ (edgeReferenceCoordinates ![f, h] z) := by
    funext z
    rfl
  rw [hfun, mvfderiv_clm_comp_apply_EDPE ℓ hχ W]
  have h0 := edgeReferenceCoordinates_derivative hGc W 0
  have h1 := edgeReferenceCoordinates_derivative hGc W 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

/-- Surjectivity of the pair differential in the pair form. -/
theorem surjective_mfderiv_pair_EFE {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x)
    (hs : ∀ y : ℝ × ℝ, ∃ W : TangentSpace I x,
      mvfderiv (I := I) f x W = y.1 ∧ mvfderiv (I := I) h x W = y.2) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (f z, h z)) x) := by
  intro y'
  let y : ℝ × ℝ := y'
  obtain ⟨W, hW1, hW2⟩ := hs y
  refine ⟨W, ?_⟩
  change mvfderiv (I := I) (fun z => (f z, h z)) x W = y
  rw [mvfderiv_pair_apply_EFE hf hh W, hW1, hW2]
  rfl

/-- Surjectivity onto the reference plane gives the pair form. -/
theorem pair_form_of_surjective_edgeReference_EFE {f h : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x)
    (hs : Surjective (mvfderiv (I := I) (edgeReferenceCoordinates ![f, h]) x)) (y : ℝ × ℝ) :
    ∃ W : TangentSpace I x, mvfderiv (I := I) f x W = y.1 ∧ mvfderiv (I := I) h x W = y.2 := by
  have hGc : ∀ k, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (![f, h] k) x := fun k => by
    fin_cases k
    · exact hf
    · exact hh
  obtain ⟨W, hW⟩ := hs (WithLp.toLp 2 ![y.1, y.2])
  refine ⟨W, ?_, ?_⟩
  · have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hW
    simp only at h0
    rw [edgeReferenceCoordinates_derivative hGc W 0] at h0
    simpa using h0
  · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hW
    simp only at h1
    rw [edgeReferenceCoordinates_derivative hGc W 1] at h1
    simpa using h1

/-- Subtracting a constant does not change the differential. -/
theorem mvfderiv_sub_const_EFE {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (c : ℝ) (w : TangentSpace I x) :
    mvfderiv (I := I) (fun z => f z - c) x w = mvfderiv (I := I) f x w := by
  have h := DifferentialGeometry.Analysis.mvfderiv_comp_apply_of_differentiableAt_GAF3
    (Ψ := fun u : ℝ => u - c) hf (by fun_prop) w
  change mvfderiv (I := I) ((fun u : ℝ => u - c) ∘ f) x w = _
  rw [h]
  simp

/-- The differential of the scalar homotopy `(1 - τ) f + τ h`. -/
theorem mvfderiv_homotopy_scalar_EFE {f h : M → ℝ} {x : M} (τ : ℝ)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) (hh : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ h x)
    (W : TangentSpace I x) :
    mvfderiv (I := I) (fun z => (1 - τ) * f z + τ * h z) x W =
      (1 - τ) * mvfderiv (I := I) f x W + τ * mvfderiv (I := I) h x W := by
  have hf' := hf.mdifferentiableAt (by simp)
  have hh' := hh.mdifferentiableAt (by simp)
  have hf'' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => (1 - τ) * f z) x :=
    (contMDiffAt_const.mul hf).mdifferentiableAt (by simp)
  have hh'' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => τ * h z) x :=
    (contMDiffAt_const.mul hh).mdifferentiableAt (by simp)
  rw [mvfderiv_fun_add hf'' hh'', add_apply, mvfderiv_const_mul _ _ hf',
    mvfderiv_const_mul _ _ hh']
  rfl

end Calculus

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The open original source `Y_j = {p ∈ B(j, 100Δρ(j)) : |η_j| < 5Δ, t < 5Δ}` of an edge chart. -/
theorem isOpen_edgeSource_EFE
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) {j : X} (hj : j ∈ L.edge.centres) :
    IsOpen {p | p ∈ ball j (100 * Δ * ρ j) ∧ |L.edge.coord j p| < 5 * Δ ∧
      L.edge.smoothing p / ρ p < 5 * Δ} := by
  have hη : IsOpen (ball j (100 * Δ * ρ j) ∩ L.edge.coord j ⁻¹' Ioo (-(5 * Δ)) (5 * Δ)) :=
    (L.edge.contMDiffOn_coord hj).continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Ioo
  have ht : IsOpen ((fun p => L.edge.smoothing p / ρ p) ⁻¹' Iio (5 * Δ)) :=
    isOpen_Iio.preimage (continuous_cgpHeight L.toLocalChartFamily)
  convert hη.inter ht using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, mem_Iio, abs_lt]
  tauto

/-- **The original LFR28 disk of an actual edge chart as a smooth embedding** into `X`, onto the
WHOLE original zero fibre `{η_j = 0, H₀ ≤ 4Δ}` of `B(j, 100Δρ(j))`, boundary circle onto the rim. -/
theorem LocalChartPacketsC14.edge_smoothDisk_EFE
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.edge.centres) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {p | p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = 0 ∧
        edgeRowHeight Δ L.edge.smoothing ρ p ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {p | p ∈ ball j (100 * Δ * ρ j) ∧
        L.edge.coord j p = 0 ∧ edgeRowHeight Δ L.edge.smoothing ρ p = 4 * Δ} := by
  have hrj := hρ j
  have hq : ∀ y, L.edge.smoothing y / ρ j / (ρ y / ρ j) = L.edge.smoothing y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hH : edgeRowHeight Δ (fun x => L.edge.smoothing x / ρ j) (fun x => ρ x / ρ j) =
      edgeRowHeight Δ L.edge.smoothing ρ := by
    funext y
    unfold edgeRowHeight
    rw [hq]
  set Bp : Set X := ball j (100 * Δ * ρ j) with hBp
  have hball : ∀ y, (ρ j)⁻¹ * dist y j < 100 * Δ ↔ y ∈ Bp := fun y => by
    rw [hBp, mem_ball, inv_mul_lt_iff₀ hrj]
    constructor <;> intro h <;> linarith
  have hD := L.edgeDisk j hj
  have hcc := L.edge.chart_center j hj
  set η := L.edge.coord j with hηdef
  set Fs := L.edge.smoothing with hFsdef
  let c := L.edge.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc : η = c.coord := by
    rw [hηdef]
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
  obtain ⟨P, hP⟩ := hD
  have hPc : P.coord = η := by
    rw [hc]
    exact congrArg EdgeChart.coord hP
  have hPb : ∀ y, y ∈ ball P.center (100 * Δ) ↔ y ∈ Bp := fun y => by
    have hcen : P.center = j := (congrArg EdgeChart.center hP).trans hcc
    rw [hcen, ← hball y]
    rfl
  obtain ⟨φ, hφ, hr, hb⟩ := P.exists_smoothDisk_EFE hΔ
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hr, hH, hPc]
    ext y
    simp only [mem_ofPred_eq, hPb]
  · rw [hb, hH, hPc]
    ext y
    simp only [mem_ofPred_eq, hPb]


/-- **EDP04, step B: the original disk at level `a`.** The whole original fibre
`{η_j = a, H₀ ≤ 4Δ}` of `B(j, 100Δρ(j))`, `|a| < 4Δ`, is the range of a smooth embedding of
`ClosedCell 2` (boundary circle onto the rim `{H₀ = 4Δ}`): E0 applied to the family
`(η_j - τ a, H₀)`, whose trace lies in EDP03's compact buffer and which is transverse (rank two on
the rim, by the collar co-norm of the ORIGINAL pair). -/
theorem LocalChartPacketsC14.edge_levelDisk_EFE
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1)
    (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) {j : X}
    (hj : j ∈ L.edge.centres) {a : ℝ} (ha : |a| < 4 * Δ) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {p | p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        edgeRowHeight Δ L.edge.smoothing ρ p ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {p | p ∈ ball j (100 * Δ * ρ j) ∧
        L.edge.coord j p = a ∧ edgeRowHeight Δ L.edge.smoothing ρ p = 4 * Δ} := by
  have hΔ0 : 0 < Δ := by linarith
  have hab := abs_nonneg a
  set η := L.edge.coord j with hηdef
  set H₀ := edgeRowHeight Δ L.edge.smoothing ρ with hH₀def
  set Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| < 5 * Δ ∧
    L.edge.smoothing p / ρ p < 5 * Δ} with hY
  have hYo : IsOpen Y := isOpen_edgeSource_EFE L hj
  obtain ⟨-, hηs, hHs, hdη, Q, hQc, hQY, hQi⟩ :=
    edp03_buffer L.toLocalChartFamilyE hΔ hμ hτ hlam hσc hb hj
  obtain ⟨φ₀, hφ₀, hφ₀r, hφ₀b⟩ := L.edge_smoothDisk_EFE hΔ0 hj
  simp only [← hηdef, ← hH₀def] at hηs hHs hdη hQY hQi hφ₀r hφ₀b
  have hmemY : ∀ p, p ∈ ball j (100 * Δ * ρ j) → |η p| < 5 * Δ → H₀ p ≤ 4 * Δ → p ∈ Y :=
    fun p hp hη hH => ⟨hp, hη, by have := (edgeRowHeight_le_iff hΔ0).mp hH; linarith⟩
  let O : TopologicalSpace.Opens X := ⟨Y, hYo⟩
  have hfst : ContMDiffOn (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ, E3) ∞ (Prod.fst : X × ℝ → X)
      ((O : Set X) ×ˢ univ) :=
    (contMDiff_fst : ContMDiff (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ, E3) ∞ (Prod.fst : X × ℝ → X)).contMDiffOn
  have hsnd : ContMDiff (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (Prod.snd : X × ℝ → ℝ) := contMDiff_snd
  have hh : ContMDiffOn (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun q : X × ℝ => η q.1 - q.2 * a)
      ((O : Set X) ×ˢ univ) :=
    (hηs.comp hfst (fun q hq => hq.1)).sub ((hsnd.mul contMDiff_const).contMDiffOn)
  have hT : ContMDiffOn (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun q : X × ℝ => H₀ q.1)
      ((O : Set X) ×ˢ univ) :=
    hHs.comp hfst (fun q hq => hq.1)
  have hηY : ∀ y ∈ Y, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ) ∞ η y := fun y hy =>
    hηs.contMDiffAt (hYo.mem_nhds hy)
  have hHY : ∀ y ∈ Y, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ) ∞ H₀ y := fun y hy =>
    hHs.contMDiffAt (hYo.mem_nhds hy)
  have hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set X), η y - τ * a = 0 → H₀ y ≤ 4 * Δ →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) (fun z => η z - τ * a) y) := by
    intro τ hτ y hy _ _
    obtain ⟨w, -, hw⟩ := hdη y hy
    have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) η y := (hηY y hy).mdifferentiableAt (by simp)
    refine surjective_mfderiv_of_mvfderiv_ne_zero_EFE (I := 𝓘(ℝ, E3))
      (f := fun z => η z - τ * a) (x := y) w ?_
    rw [mvfderiv_sub_const_EFE hηd]
    exact (lt_trans (by norm_num) hw).ne'
  have hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set X), η y - τ * a = 0 → H₀ y = 4 * Δ →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) (fun z => (η z - τ * a, H₀ z)) y) := by
    intro τ hτ y hy _ hT4
    have ht4 : L.edge.smoothing y / ρ y = 4 * Δ := (edgeRowHeight_eq_four_iff_EDP3 hΔ0).mp hT4
    obtain ⟨-, -, hsurj, -⟩ := L.edge.collar_height_conorm_EDP3 hγc hγc1 hβc1 hΔ0 hj hy.1 hy.2.1
      (by linarith) (by linarith)
    refine surjective_mfderiv_pair_EFE (f := fun z => η z - τ * a) (h := H₀)
      ((hηY y hy).sub contMDiffAt_const) (hHY y hy) ?_
    intro yy
    obtain ⟨W, hW1, hW2⟩ := pair_form_of_surjective_edgeReference_EFE (hηY y hy) (hHY y hy)
      hsurj yy
    refine ⟨W, ?_, hW2⟩
    rw [mvfderiv_sub_const_EFE ((hηY y hy).mdifferentiableAt (by simp))]
    exact hW1
  have hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set X), η y - τ * a = 0 → H₀ y ≤ 4 * Δ →
      y ∈ Q := by
    intro τ hτ y hy hηa hH
    have hηle : |η y| ≤ |a| := by
      have : η y = τ * a := by linarith
      rw [this, abs_mul, abs_of_nonneg hτ.1]
      exact mul_le_of_le_one_left (abs_nonneg a) hτ.2
    have ht := (edgeRowHeight_le_iff hΔ0).mp hH
    exact interior_subset (hQi ⟨hy.1, by linarith, by linarith⟩)
  have hφ₀r' : range φ₀ = {y | y ∈ (O : Set X) ∧ η y - 0 * a = 0 ∧ H₀ y ≤ 4 * Δ} := by
    rw [hφ₀r]
    ext p
    constructor
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hmemY p hp (by rw [hη, abs_zero]; positivity) hH, by rw [hη]; ring, hH⟩
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hp.1, by linarith, hH⟩
  have hφ₀b' : range (φ₀ ∘ cellBoundaryInclusion 2) =
      {y | y ∈ (O : Set X) ∧ η y - 0 * a = 0 ∧ H₀ y = 4 * Δ} := by
    rw [hφ₀b]
    ext p
    constructor
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hmemY p hp (by rw [hη, abs_zero]; positivity) hH.le, by rw [hη]; ring, hH⟩
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hp.1, by linarith, hH⟩
  obtain ⟨φ, hφ, hr, hb', -⟩ :=
    DifferentialGeometry.Topology.Ehresmann.wholeDisk_of_compact_transverse_trace_opens_EFC
      (I := 𝓘(ℝ, E3)) O
    (fun q : X × ℝ => η q.1 - q.2 * a) (fun q : X × ℝ => H₀ q.1) hh hT 0 (4 * Δ) hreg hface hQc
    hQY hloc hφ₀ hφ₀r' hφ₀b'
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hr]
    ext p
    constructor
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hp.1, by linarith, hH⟩
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hmemY p hp (by rw [hη]; linarith) hH, by linarith, hH⟩
  · rw [hb']
    ext p
    constructor
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hp.1, by linarith, hH⟩
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hmemY p hp (by rw [hη]; linarith) hH.le, by linarith, hH⟩

end DifferentialGeometry.Geometry.Collapse
