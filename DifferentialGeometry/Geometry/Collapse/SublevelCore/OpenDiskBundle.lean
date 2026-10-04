import DifferentialGeometry.Geometry.Comparison.Soul.NormalFlowGluing
import DifferentialGeometry.Geometry.Comparison.Soul.NormalBundleCompactness
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The open unit disk bundle is diffeomorphic to the whole bundle (kernel of LC61)

Frozen blueprint master207A, corollary `cor:collapse-joint-open-ball-type` (LC61, lines
23460–23495). Its proof identifies the interior of the closed unit normal disk bundle with the
entire normal bundle by the mutually inverse fibrewise maps
`v ↦ v / √(1 - ‖v‖²)` and `z ↦ z / √(1 + ‖z‖²)`, smooth also at the zero section because the
squared norm is smooth and the denominators are positive.

We prove this for ANY smooth vector bundle `V → B` and any smooth function `Q ≥ 0` on its total
space that is fibrewise homogeneous of degree two (`Q (c • v) = c² Q v`), e.g. the squared length of
a smooth fibre metric. The output is a `PartialDiffeomorph` of the total space with source
`{Q < 1}` and target everything, given by the displayed formula. The instance for the PC soul normal
bundle (squared `g`-length) is `exists_soul_normal_openDisk_partialDiffeomorph`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

section FiberScaling

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Fibrewise scalar multiplication `(c, z) ↦ c • z` is smooth on the total space. -/
theorem contMDiff_totalSpace_smul :
    ContMDiff (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) ∞
      (fun z : ℝ × TotalSpace F V => (⟨z.2.proj, z.1 • z.2.snd⟩ : TotalSpace F V)) := by
  intro z
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) ∞
      (Prod.snd : ℝ × TotalSpace F V → TotalSpace F V) z := contMDiffAt_snd
  obtain ⟨hb, hv⟩ := Bundle.contMDiffAt_totalSpace.mp hs
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hb, (contMDiffAt_fst.smul hv).congr_of_eventuallyEq ?_⟩
  let e := trivializationAt F V z.2.proj
  have he : ∀ᶠ y : ℝ × TotalSpace F V in 𝓝 z, y.2.proj ∈ e.baseSet :=
    hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V z.2.proj))
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul y.1 y.2.snd

/-- Scaling by a scalar function that is smooth on an open set is smooth there. -/
theorem contMDiffOn_totalSpace_smul_of_contMDiffOn {f : TotalSpace F V → ℝ}
    {s : Set (TotalSpace F V)} (hf : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ f s) :
    ContMDiffOn (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace F V => (⟨z.proj, f z • z.snd⟩ : TotalSpace F V)) s :=
  (contMDiff_totalSpace_smul (IB := IB) (F := F) (V := V)).comp_contMDiffOn
    (hf.prodMk contMDiffOn_id)

/-- **Kernel of LC61.** For a smooth fibrewise-quadratic `Q ≥ 0`, the open "unit disk bundle"
`{Q < 1}` is diffeomorphic to the whole total space by `z ↦ (√(1 - Q z))⁻¹ • z`, with inverse
`w ↦ (√(1 + Q w))⁻¹ • w`; both preserve fibres. -/
theorem exists_openDisk_partialDiffeomorph (Q : TotalSpace F V → ℝ)
    (hQ : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ Q) (hQ0 : ∀ z, 0 ≤ Q z)
    (hQsmul : ∀ (c : ℝ) (z : TotalSpace F V), Q ⟨z.proj, c • z.snd⟩ = c ^ 2 * Q z) :
    ∃ Ψ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F))
        (TotalSpace F V) (TotalSpace F V) ∞,
      Ψ.source = {z | Q z < 1} ∧ Ψ.target = univ ∧
      (∀ z, Ψ z = ⟨z.proj, (Real.sqrt (1 - Q z))⁻¹ • z.snd⟩) ∧
      ∀ w, Ψ.symm w = ⟨w.proj, (Real.sqrt (1 + Q w))⁻¹ • w.snd⟩ := by
  classical
  let fwd : TotalSpace F V → TotalSpace F V := fun z => ⟨z.proj, (Real.sqrt (1 - Q z))⁻¹ • z.snd⟩
  let bwd : TotalSpace F V → TotalSpace F V := fun w => ⟨w.proj, (Real.sqrt (1 + Q w))⁻¹ • w.snd⟩
  have hsource : IsOpen {z : TotalSpace F V | Q z < 1} := isOpen_lt hQ.continuous continuous_const
  -- The two scalar coefficients are smooth where they are used.
  have hcoef₁ : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
      (fun z => (Real.sqrt (1 - Q z))⁻¹) {z | Q z < 1} := by
    intro z hz
    have hpos : 0 < 1 - Q z := by simp only [mem_ofPred_eq] at hz; linarith
    have hsq : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.sqrt x)⁻¹) (1 - Q z) :=
      (Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
    exact (hsq.contMDiffAt.comp z ((contMDiffAt_const.sub (hQ z)))).contMDiffWithinAt
  have hcoef₂ : ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
      (fun w => (Real.sqrt (1 + Q w))⁻¹) univ := by
    intro w _
    have hpos : 0 < 1 + Q w := by linarith [hQ0 w]
    have hsq : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.sqrt x)⁻¹) (1 + Q w) :=
      (Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
    exact (hsq.contMDiffAt.comp w ((contMDiffAt_const.add (hQ w)))).contMDiffWithinAt
  -- Algebra of the coefficients.
  have hQfwd : ∀ z, Q z < 1 → Q (fwd z) = Q z / (1 - Q z) := by
    intro z hz
    have hpos : 0 < 1 - Q z := by linarith
    change Q ⟨z.proj, _⟩ = _
    rw [hQsmul, inv_pow, Real.sq_sqrt hpos.le]
    field_simp
  have hQbwd : ∀ w, Q (bwd w) = Q w / (1 + Q w) := by
    intro w
    have hpos : 0 < 1 + Q w := by linarith [hQ0 w]
    change Q ⟨w.proj, _⟩ = _
    rw [hQsmul, inv_pow, Real.sq_sqrt hpos.le]
    field_simp
  have hleft : ∀ z, Q z < 1 → bwd (fwd z) = z := by
    intro z hz
    have hpos : 0 < 1 - Q z := by linarith
    have hone : 1 + Q (fwd z) = (1 - Q z)⁻¹ := by
      rw [hQfwd z hz]
      field_simp
      ring
    change (⟨z.proj, (Real.sqrt (1 + Q (fwd z)))⁻¹ • (Real.sqrt (1 - Q z))⁻¹ • z.snd⟩ :
      TotalSpace F V) = z
    rw [hone, Real.sqrt_inv, inv_inv, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne',
      one_smul]
  have hright : ∀ w, fwd (bwd w) = w := by
    intro w
    have hpos : 0 < 1 + Q w := by linarith [hQ0 w]
    have hone : 1 - Q (bwd w) = (1 + Q w)⁻¹ := by
      rw [hQbwd w]
      field_simp
      ring
    change (⟨w.proj, (Real.sqrt (1 - Q (bwd w)))⁻¹ • (Real.sqrt (1 + Q w))⁻¹ • w.snd⟩ :
      TotalSpace F V) = w
    rw [hone, Real.sqrt_inv, inv_inv, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne',
      one_smul]
  have hmaps : ∀ w, Q (bwd w) < 1 := by
    intro w
    have hpos : 0 < 1 + Q w := by linarith [hQ0 w]
    rw [hQbwd w, div_lt_one hpos]
    linarith
  refine ⟨{ toFun := fwd
            invFun := bwd
            source := {z | Q z < 1}
            target := univ
            map_source' := fun _ _ => mem_univ _
            map_target' := fun w _ => hmaps w
            left_inv' := fun z hz => hleft z hz
            right_inv' := fun w _ => hright w
            open_source := hsource
            open_target := isOpen_univ
            contMDiffOn_toFun := contMDiffOn_totalSpace_smul_of_contMDiffOn hcoef₁
            contMDiffOn_invFun := contMDiffOn_totalSpace_smul_of_contMDiffOn hcoef₂ },
    rfl, rfl, fun _ => rfl, fun _ => rfl⟩

end FiberScaling

section SoulNormalBundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- **LC61 kernel for the PC soul normal bundle.** The open unit normal disk bundle (squared
`g`-length `< 1`) of a totally convex boundaryless `S` is diffeomorphic to the whole normal bundle
by `v ↦ v / √(1 - |v|²)`, preserving fibres and the zero section. -/
theorem exists_soul_normal_openDisk_partialDiffeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {S : Set M} (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ∃ Ψ : PartialDiffeomorph
        ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
          𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))
        ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
          𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))
        (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ) (normalBundleFiber g S))
        (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ) (normalBundleFiber g S)) ∞,
      Ψ.source = {z | g.inner z.proj.1 z.snd.1 z.snd.1 < 1} ∧ Ψ.target = univ ∧
      ∀ z, Ψ z = ⟨z.proj, (Real.sqrt (1 - g.inner z.proj.1 z.snd.1 z.snd.1))⁻¹ • z.snd⟩ := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  have hQ : ContMDiff ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
        𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber g S) => g.inner z.proj.1 z.snd.1 z.snd.1) :=
    (tangentSquaredLength_contMDiff g).comp (normalBundleInclusion_contMDiff g hEnorm hconv hB)
  obtain ⟨Ψ, hs, ht, hΨ, -⟩ := exists_openDisk_partialDiffeomorph
    (fun z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber g S) => g.inner z.proj.1 z.snd.1 z.snd.1) hQ
    (fun z => gInner_self_nonneg g z.proj.1 z.snd.1)
    (fun c z => by
      change g.inner z.proj.1 (c • z.snd.1) (c • z.snd.1) = _
      rw [gInner_smul_self])
  exact ⟨Ψ, hs, ht, hΨ⟩

end SoulNormalBundle

end DifferentialGeometry.Geometry.Collapse
