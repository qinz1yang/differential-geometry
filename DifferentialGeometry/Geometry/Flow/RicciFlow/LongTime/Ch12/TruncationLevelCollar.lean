import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationLevel

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.LongTime.CuspP1
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {H : FiniteVolumeHyperbolicModel.{u}}

/-- **(2) Metric formula on the level-`S` cusp**: `dz² + e^{-(S+z)} q`. -/
theorem truncationAtLevel_metric_formula_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    (i : Fin T.count) (p : CuspHalfSpace) (v w : TangentSpace halfCollarModel p) :
    H.metric.inner ((truncationAtLevel_C1 T hS).cuspMap i p)
      (mfderiv halfCollarModel (𝓡 3) ((truncationAtLevel_C1 T hS).cuspMap i) p v)
      (mfderiv halfCollarModel (𝓡 3) ((truncationAtLevel_C1 T hS).cuspMap i) p w) =
      v.2 0 * w.2 0 + Real.exp (-(S + p.2.val 0)) * (T.cusp i).torusMetric.inner p.1 v.1 w.1 := by
  have h1 := (truncationAtLevel_C1 T hS).cuspIsometry i p v w
  have h2 := ((truncationAtLevel_C1 T hS).cusp i).metric_formula p v w
  rw [h1, h2, truncationAtLevel_cusp_torusMetric_C1 T hS i p.1 v.1 w.1, neg_add, Real.exp_add]
  ring

/-- The depth-`D` collar of the level-`S` truncation: `cuspMap_S '' (T² × [0,D])`. -/
def levelCollar_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S) (i : Fin T.count) (D : ℝ) :
    Set H.Carrier :=
  (truncationAtLevel_C1 T hS).cuspMap i '' (univ ×ˢ {u : EuclideanHalfSpace 1 | u.val 0 ≤ D})

/-- **(2) depth-`D` collar embedding** (`D = 200` is the case used downstream): compact image,
the parametrization is a smooth embedding (hence a topological embedding on `T² × [0,D]`), the
collar meets the new core exactly in the boundary torus, and the collars of distinct cusps are
disjoint. -/
theorem levelCollar_embedding_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    {D : ℝ} (hD : 0 ≤ D) :
    (∀ i, IsSmoothEmbedding halfCollarModel (𝓡 3) ∞ ((truncationAtLevel_C1 T hS).cuspMap i)) ∧
    (∀ i, IsCompact (levelCollar_C1 T hS i D)) ∧
    (∀ i, _root_.Topology.IsEmbedding
      (fun p : {p : CuspHalfSpace | p.2.val 0 ≤ D} => (truncationAtLevel_C1 T hS).cuspMap i p.val)) ∧
    (∀ i, range (truncationAtLevel_C1 T hS).inclusion ∩ levelCollar_C1 T hS i D =
      range (fun x : Torus => (truncationAtLevel_C1 T hS).cuspMap i (x, halfZero))) ∧
    (∀ i j, i ≠ j → Disjoint (levelCollar_C1 T hS i D) (levelCollar_C1 T hS j D)) := by
  set T' := truncationAtLevel_C1 T hS with hT'
  have hsub : ∀ i, levelCollar_C1 T hS i D ⊆ range (T'.cuspMap i) := fun i => image_subset_range _ _
  refine ⟨fun i => T'.cuspEmbedding i, fun i => ?_, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · exact ((isCompact_univ).prod (isCompact_halfSegment_CPA2 hD)).image
      (T'.cuspEmbedding i).contMDiff.continuous
  · exact (T'.cuspEmbedding i).isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
  · apply Subset.antisymm
    · rintro p ⟨hp1, hp2⟩
      have := T'.intersection i
      have hp3 : p ∈ range T'.inclusion ∩ range (T'.cuspMap i) := ⟨hp1, hsub i hp2⟩
      rwa [this] at hp3
    · intro p hp
      have : p ∈ range T'.inclusion ∩ range (T'.cuspMap i) := by rw [T'.intersection i]; exact hp
      obtain ⟨x, rfl⟩ := hp
      refine ⟨this.1, ⟨(x, halfZero), ⟨trivial, ?_⟩, rfl⟩⟩
      change (0 : ℝ) ≤ D
      exact hD
  · exact (T'.cusp_disjoint hij).mono (hsub i) (hsub j)

/-- Speed of a curve inside the slice at height `z`: `e^{-(S+z)} · q`-speed². -/
theorem truncationAtLevel_slice_speed_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    (i : Fin T.count) (c : ℝ → Torus) (hc : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ c) {z : ℝ} (hz : 0 ≤ z)
    (s : ℝ) :
    let f : ℝ → H.Carrier := fun s => (truncationAtLevel_C1 T hS).cuspMap i (c s, halfSpaceOneLift z)
    H.metric.inner (f s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) f s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) f s 1) =
      Real.exp (-(S + z)) * (T.cusp i).torusMetric.inner (c s) (mfderiv 𝓘(ℝ, ℝ) torusModel c s 1)
        (mfderiv 𝓘(ℝ, ℝ) torusModel c s 1) := by
  intro f
  set T' := truncationAtLevel_C1 T hS with hT'
  let γ : ℝ → CuspHalfSpace := fun s => (c s, halfSpaceOneLift z)
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel γ s :=
    ((hc.mdifferentiable (by simp)) s).prodMk
      ((contMDiff_const (n := ∞) (c := halfSpaceOneLift z)).mdifferentiableAt (by simp))
  have hde : MDifferentiableAt halfCollarModel (𝓡 3) (T'.cuspMap i) (γ s) :=
    (T'.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) f s =
      (mfderiv halfCollarModel (𝓡 3) (T'.cuspMap i) (γ s)).comp (mfderiv 𝓘(ℝ, ℝ) halfCollarModel γ s) :=
    mfderiv_comp s hde hγ
  have hγd : mfderiv 𝓘(ℝ, ℝ) halfCollarModel γ s 1 =
      ((mfderiv 𝓘(ℝ, ℝ) torusModel c s 1, (0 : TangentSpace (𝓡∂ 1) (halfSpaceOneLift z))) :
        TangentSpace halfCollarModel (γ s)) := by
    have := mfderiv_prodMk (I := 𝓘(ℝ, ℝ)) (I' := torusModel) (I'' := 𝓡∂ 1) (f := c)
      (g := fun _ : ℝ => halfSpaceOneLift z) (x := s) (hc.mdifferentiable (by simp) s)
      ((contMDiff_const (n := ∞) (c := halfSpaceOneLift z)).mdifferentiableAt (by simp))
    change mfderiv 𝓘(ℝ, ℝ) halfCollarModel (fun s => (c s, halfSpaceOneLift z)) s 1 = _
    rw [this]
    simp [mfderiv_const]
    rfl
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hγd]
  have key := truncationAtLevel_metric_formula_C1 T hS i (γ s)
    ((mfderiv 𝓘(ℝ, ℝ) torusModel c s 1, (0 : TangentSpace (𝓡∂ 1) (halfSpaceOneLift z))) :
        TangentSpace halfCollarModel (γ s))
    ((mfderiv 𝓘(ℝ, ℝ) torusModel c s 1, (0 : TangentSpace (𝓡∂ 1) (halfSpaceOneLift z))) :
        TangentSpace halfCollarModel (γ s))
  have hz' : (γ s).2.val 0 = z := halfSpaceOneLift_val_CPA2 hz
  rw [hz'] at key
  refine key.trans ?_
  change (0 : ℝ) * 0 + _ = _
  rw [zero_mul, zero_add]

/-- **(3) Cross-section diameter decay, explicit bound.** If `x, y` of the original cusp
cross-section are joined by a smooth curve of `q`-speed `≤ D`, then the images `cuspMap_S(x,z)`,
`cuspMap_S(y,z)` in `H` are joined by a smooth curve of `H`-speed `≤ e^{-(S+z)/2} D ≤ e^{-S/2} D`
(`z ≥ 0`), so the slice at depth `z` has intrinsic diameter `≤ e^{-(S+z)/2} · diam_q → 0`
as `S → ∞`. -/
theorem truncationAtLevel_slice_connect_C1 (T : HyperbolicTruncation H) {S : ℝ} (hS : 2 ≤ S)
    (i : Fin T.count) (x y : Torus) {D : ℝ} (c : ℝ → Torus)
    (hc : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ c) (h0 : c 0 = x) (h1 : c 1 = y)
    (hD : ∀ s, (T.cusp i).torusMetric.inner (c s) (mfderiv 𝓘(ℝ, ℝ) torusModel c s 1)
      (mfderiv 𝓘(ℝ, ℝ) torusModel c s 1) ≤ D ^ 2) {z : ℝ} (hz : 0 ≤ z) :
    ∃ f : ℝ → H.Carrier, ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ f ∧
      f 0 = (truncationAtLevel_C1 T hS).cuspMap i (x, halfSpaceOneLift z) ∧
      f 1 = (truncationAtLevel_C1 T hS).cuspMap i (y, halfSpaceOneLift z) ∧
      ∀ s, H.metric.inner (f s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) f s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) f s 1) ≤
        (Real.exp (-(S + z) / 2) * D) ^ 2 ∧ Real.exp (-(S + z) / 2) ≤ Real.exp (-S / 2) := by
  refine ⟨fun s => (truncationAtLevel_C1 T hS).cuspMap i (c s, halfSpaceOneLift z), ?_, ?_, ?_,
    fun s => ⟨?_, Real.exp_le_exp.mpr (by linarith)⟩⟩
  · exact ((truncationAtLevel_C1 T hS).cuspEmbedding i).contMDiff.comp
      (hc.prodMk contMDiff_const)
  · simp [h0]
  · simp [h1]
  · rw [truncationAtLevel_slice_speed_C1 T hS i c hc hz s, mul_pow, ← Real.exp_nat_mul]
    have : (↑(2 : ℕ) : ℝ) * (-(S + z) / 2) = -(S + z) := by push_cast; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (hD s) (Real.exp_pos _).le

end GC.LongTime.Ch12
