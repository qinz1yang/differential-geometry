import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle

/-!
# Radial normalization outside a disk bundle (the end-count step of LFR52)

Frozen blueprint master207A, lemma `lem:collapse-twisted-core-identifications` (LFR52, lines
29380–29437), end assertions: "Outside one such disk, radial normalization is a smooth product
`S(Ê) × (R, ∞)`. Hence its number of ends is the number of components of the unit sphere bundle."

For ANY smooth vector bundle and any smooth fibrewise-quadratic `Q` (`Q (c • z) = c² Q z`, e.g. the
squared length of a fibre metric), the region `{Q > R²}` outside the closed `R`-disk bundle is
homeomorphic to `{Q = 1} × (R, ∞)` by `z ↦ (z / √(Q z), √(Q z))`, with inverse `(u, t) ↦ t • u`
(`exists_radialProduct_homeomorph`). Consequently that region is connected iff the unit sphere
bundle is (`connectedSpace_outside_iff`). The tree has no notion of ends; the cofinality of the
closed disk bundles and the end count itself are not formalized here. The instance for the PC soul
normal bundle is `exists_soul_normal_radialProduct_homeomorph`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

section Radial

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **LFR52, radial product kernel.** Outside the closed `R`-disk bundle `{Q ≤ R²}`, radial
normalization identifies the total space with `{Q = 1} × (R, ∞)`. -/
theorem exists_radialProduct_homeomorph (Q : TotalSpace F V → ℝ)
    (hQ : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ Q)
    (hQsmul : ∀ (c : ℝ) (z : TotalSpace F V), Q ⟨z.proj, c • z.snd⟩ = c ^ 2 * Q z)
    {R : ℝ} (hR : 0 < R) :
    ∃ Θ : {z : TotalSpace F V // R ^ 2 < Q z} ≃ₜ {z : TotalSpace F V // Q z = 1} × Ioi R,
      (∀ z, ((Θ z).1 : TotalSpace F V) = ⟨z.1.proj, (Real.sqrt (Q z.1))⁻¹ • z.1.snd⟩ ∧
        ((Θ z).2 : ℝ) = Real.sqrt (Q z.1)) ∧
      ∀ (u : {z : TotalSpace F V // Q z = 1}) (t : Ioi R),
        ((Θ.symm (u, t)) : TotalSpace F V) = ⟨u.1.proj, (t : ℝ) • u.1.snd⟩ := by
  have hsmul : Continuous (fun z : ℝ × TotalSpace F V =>
      (⟨z.2.proj, z.1 • z.2.snd⟩ : TotalSpace F V)) :=
    (contMDiff_totalSpace_smul (IB := IB) (F := F) (V := V)).continuous
  have hQc : Continuous Q := hQ.continuous
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hpos (z : {z : TotalSpace F V // R ^ 2 < Q z}) : 0 < Q z.1 := lt_of_le_of_lt hR2 z.2
  have hsqrt (z : {z : TotalSpace F V // R ^ 2 < Q z}) : 0 < Real.sqrt (Q z.1) :=
    Real.sqrt_pos.mpr (hpos z)
  have hunit (z : {z : TotalSpace F V // R ^ 2 < Q z}) :
      Q ⟨z.1.proj, (Real.sqrt (Q z.1))⁻¹ • z.1.snd⟩ = 1 := by
    rw [hQsmul, inv_pow, Real.sq_sqrt (hpos z).le, inv_mul_cancel₀ (hpos z).ne']
  have hlarge (z : {z : TotalSpace F V // R ^ 2 < Q z}) : R < Real.sqrt (Q z.1) := by
    calc R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hR.le).symm
      _ < Real.sqrt (Q z.1) := Real.sqrt_lt_sqrt hR2 z.2
  have hout (u : {z : TotalSpace F V // Q z = 1}) (t : Ioi R) :
      R ^ 2 < Q ⟨u.1.proj, (t : ℝ) • u.1.snd⟩ := by
    rw [hQsmul, u.2, mul_one]
    exact pow_lt_pow_left₀ t.2 hR.le two_ne_zero
  let fwd : {z : TotalSpace F V // R ^ 2 < Q z} → {z : TotalSpace F V // Q z = 1} × Ioi R :=
    fun z => (⟨⟨z.1.proj, (Real.sqrt (Q z.1))⁻¹ • z.1.snd⟩, hunit z⟩,
      ⟨Real.sqrt (Q z.1), hlarge z⟩)
  let bwd : {z : TotalSpace F V // Q z = 1} × Ioi R → {z : TotalSpace F V // R ^ 2 < Q z} :=
    fun p => ⟨⟨p.1.1.proj, (p.2 : ℝ) • p.1.1.snd⟩, hout p.1 p.2⟩
  have hcoef : Continuous (fun z : {z : TotalSpace F V // R ^ 2 < Q z} =>
      (Real.sqrt (Q z.1))⁻¹) :=
    (Real.continuous_sqrt.comp (hQc.comp continuous_subtype_val)).inv₀ fun z => (hsqrt z).ne'
  have hfwd : Continuous fwd := by
    refine Continuous.prodMk ?_ ?_
    · exact (hsmul.comp (hcoef.prodMk continuous_subtype_val)).subtype_mk _
    · exact (Real.continuous_sqrt.comp (hQc.comp continuous_subtype_val)).subtype_mk _
  have hbwd : Continuous bwd := by
    refine Continuous.subtype_mk ?_ _
    exact hsmul.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst))
  have hleft : Function.LeftInverse bwd fwd := by
    intro z
    apply Subtype.ext
    change (⟨z.1.proj, Real.sqrt (Q z.1) • (Real.sqrt (Q z.1))⁻¹ • z.1.snd⟩ :
      TotalSpace F V) = z.1
    rw [smul_smul, mul_inv_cancel₀ (hsqrt z).ne', one_smul]
  have hright : Function.RightInverse bwd fwd := by
    rintro ⟨u, t⟩
    have hQt : Q (bwd (u, t)).1 = (t : ℝ) ^ 2 := by
      change Q ⟨u.1.proj, (t : ℝ) • u.1.snd⟩ = _
      rw [hQsmul, u.2, mul_one]
    have ht : 0 < (t : ℝ) := hR.trans t.2
    have hst : Real.sqrt (Q (bwd (u, t)).1) = t := by
      rw [hQt, Real.sqrt_sq ht.le]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext hst)
    change (⟨u.1.proj, (Real.sqrt (Q (bwd (u, t)).1))⁻¹ • (t : ℝ) • u.1.snd⟩ :
      TotalSpace F V) = u.1
    rw [hst, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  refine ⟨⟨⟨fwd, bwd, hleft, hright⟩, hfwd, hbwd⟩, fun z => ⟨rfl, rfl⟩, fun u t => rfl⟩

/-- **LFR52, connectedness outside a disk bundle.** The region outside the closed `R`-disk bundle
is connected iff the unit sphere bundle `{Q = 1}` is connected. -/
theorem connectedSpace_outside_iff {Q : TotalSpace F V → ℝ}
    (hQ : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ Q)
    (hQsmul : ∀ (c : ℝ) (z : TotalSpace F V), Q ⟨z.proj, c • z.snd⟩ = c ^ 2 * Q z)
    {R : ℝ} (hR : 0 < R) :
    ConnectedSpace {z : TotalSpace F V // R ^ 2 < Q z} ↔
      ConnectedSpace {z : TotalSpace F V // Q z = 1} := by
  obtain ⟨Θ, -, -⟩ := exists_radialProduct_homeomorph Q hQ hQsmul hR
  have : ConnectedSpace (Ioi R) := Subtype.connectedSpace isConnected_Ioi
  have : Nonempty (Ioi R) := ⟨⟨R + 1, by simp⟩⟩
  constructor
  · intro h
    have : ConnectedSpace ({z : TotalSpace F V // Q z = 1} × Ioi R) :=
      Θ.surjective.connectedSpace Θ.continuous
    exact (Prod.fst_surjective (α := {z : TotalSpace F V // Q z = 1}) (β := Ioi R)).connectedSpace
      continuous_fst
  · intro h
    exact Θ.symm.surjective.connectedSpace Θ.symm.continuous

end Radial

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

/-- **LFR52 radial product for the PC soul normal bundle.** Outside the closed `R`-disk bundle
(squared `g`-length `≤ R²`), the normal bundle of a totally convex boundaryless `S` is the product
of its unit sphere bundle with `(R, ∞)`, by radial normalization. -/
theorem exists_soul_normal_radialProduct_homeomorph
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {S : Set M} (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) {R : ℝ} (hR : 0 < R) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ∃ Θ : {z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
          (normalBundleFiber g S) // R ^ 2 < g.inner z.proj.1 z.snd.1 z.snd.1} ≃ₜ
        {z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
          (normalBundleFiber g S) // g.inner z.proj.1 z.snd.1 z.snd.1 = 1} × Ioi R,
      ∀ u t, ((Θ.symm (u, t)) : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
          (normalBundleFiber g S)) = ⟨u.1.proj, (t : ℝ) • u.1.snd⟩ := by
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
  obtain ⟨Θ, -, hΘ⟩ := exists_radialProduct_homeomorph
    (fun z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber g S) => g.inner z.proj.1 z.snd.1 z.snd.1) hQ
    (fun c z => by
      change g.inner z.proj.1 (c • z.snd.1) (c • z.snd.1) = _
      rw [gInner_smul_self]) hR
  exact ⟨Θ, hΘ⟩

end SoulNormalBundle

end DifferentialGeometry.Geometry.Collapse
