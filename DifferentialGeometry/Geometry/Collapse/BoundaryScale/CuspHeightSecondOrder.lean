import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightDifferential
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryApplications
import DifferentialGeometry.Topology.Manifold.Diffeomorph.InvFunOnSmoothTwo

/-!
# The collar height is `C²` up to the boundary

For a cusp embedding `e : CuspEmbedding W g K δ X` with `K ≥ 1` (so `e` is `C²`):

* `CuspEmbedding.contMDiffOn_invFunOn_two`: the inverse `invFunOn e.toFun cuspDomain` is `C²` on
  the open collar `e '' cuspDomain`, boundary points included;
* `CuspEmbedding.contMDiffOn_height_invFunOn_two`: hence so is the collar height
  `ζ = z ∘ e⁻¹`;
* `CuspEmbedding.mfderiv_invFunOn_inverse`, `CuspEmbedding.mpullback_invFunOn_apply`: the
  derivative of the inverse at `e q` is `(De q)⁻¹`, so the pullback by the inverse of a vector
  field `V` on the cusp is its pushforward, `(e⁻¹)^* V (e q) = De q (V q)`;
* `CuspEmbedding.contMDiffAt_pullback_inner`: `q ↦ g(De q U q, De q U' q)` is `C¹` for `C¹`
  vector fields `U, U'`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "Ec" => (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- **The inverse coordinate is `C²` up to the boundary** (`K ≥ 1`). -/
theorem CuspEmbedding.contMDiffOn_invFunOn_two (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K) :
    ContMDiffOn W.model halfCollarModel 2 (invFunOn e.toFun cuspDomain)
      (e.toFun '' cuspDomain) :=
  Topology.Manifold.contMDiffOn_invFunOn_two_of_isInvertible_mfderiv isOpen_cuspDomain
    (e.contMDiffOn.of_le (by exact_mod_cast Nat.add_le_add_right hK 1)) e.injOn_cuspDomain
    (fun _ hV hVo => e.isOpen_image hVo hV) fun _ hp => e.isInvertible_mfderiv hp

/-- **The collar height `z ∘ e⁻¹` is `C²` on the open collar**, boundary included (`K ≥ 1`). -/
theorem CuspEmbedding.contMDiffOn_height_invFunOn_two (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) :
    ContMDiffOn W.model 𝓘(ℝ, ℝ) 2 (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
      (e.toFun '' cuspDomain) := by
  have hz : ContMDiff halfCollarModel 𝓘(ℝ, ℝ) 2
      ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) ∘ (𝓡∂ 1) ∘
        Prod.snd) :=
    (ContinuousLinearMap.contMDiff _).comp ((𝓡∂ 1).contMDiff.comp
      (contMDiff_snd (M := Torus) (N := EuclideanHalfSpace 1)))
  exact hz.comp_contMDiffOn (e.contMDiffOn_invFunOn_two hK)

/-- The derivative of the inverse coordinate at `e q` is a left inverse of `De q`. -/
theorem CuspEmbedding.mfderiv_invFunOn_comp_mfderiv (e : CuspEmbedding W g K δ X)
    {q : CuspHalfSpace} (hq : q ∈ cuspDomain) (v : TangentSpace halfCollarModel q) :
    mfderiv W.model halfCollarModel (invFunOn e.toFun cuspDomain) (e.toFun q)
        (mfderiv halfCollarModel W.model e.toFun q v) = v := by
  have heq : e.toFun q ∈ e.toFun '' cuspDomain := mem_image_of_mem _ hq
  have hinvd : MDifferentiableAt W.model halfCollarModel (invFunOn e.toFun cuspDomain)
      (e.toFun q) :=
    (e.contMDiffOn_invFunOn.contMDiffAt
      (e.isOpen_image_cuspDomain.mem_nhds heq)).mdifferentiableAt one_ne_zero
  have hed : MDifferentiableAt halfCollarModel W.model e.toFun q :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hq)).mdifferentiableAt (by simp)
  have hloc : (invFunOn e.toFun cuspDomain ∘ e.toFun) =ᶠ[𝓝 q] id := by
    filter_upwards [isOpen_cuspDomain.mem_nhds hq] with r hr
    exact e.injOn_cuspDomain.leftInvOn_invFunOn hr
  have h := mfderiv_comp_apply q hinvd hed v
  rw [hloc.mfderiv_eq, mfderiv_id] at h
  exact h.symm

/-- The inverse of the derivative of the inverse coordinate at `e q` is `De q` (as maps between
the model spaces). -/
theorem CuspEmbedding.mfderiv_invFunOn_inverse (e : CuspEmbedding W g K δ X)
    {q : CuspHalfSpace} (hq : q ∈ cuspDomain) :
    (mfderiv W.model halfCollarModel (invFunOn e.toFun cuspDomain) (e.toFun q) :
        EuclideanSpace ℝ (Fin 3) →L[ℝ]
          ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))).inverse =
      (mfderiv halfCollarModel W.model e.toFun q :
        ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)) := by
  obtain ⟨A₀, hA⟩ := e.isInvertible_mfderiv hq
  let A : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) := A₀
  let L : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) := mfderiv halfCollarModel W.model e.toFun q
  let Mi : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) :=
    mfderiv W.model halfCollarModel (invFunOn e.toFun cuspDomain) (e.toFun q)
  have hML : ∀ v, Mi (L v) = v := fun v => e.mfderiv_invFunOn_comp_mfderiv hq v
  have hAL : (A : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
      →L[ℝ] EuclideanSpace ℝ (Fin 3)) = L := hA
  have hMi : Mi = (A.symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))) := by
    refine ContinuousLinearMap.ext fun u => ?_
    have h := hML (A.symm u)
    rw [← hAL] at h
    simpa using h
  change Mi.inverse = L
  rw [hMi, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.symm_symm]
  exact hAL

/-- The pullback of a vector field on the cusp by the inverse coordinate is its pushforward
by `e`. -/
theorem CuspEmbedding.mpullback_invFunOn_apply (e : CuspEmbedding W g K δ X)
    {q : CuspHalfSpace} (hq : q ∈ cuspDomain)
    (V : (r : CuspHalfSpace) → TangentSpace halfCollarModel r) :
    VectorField.mpullback W.model halfCollarModel (invFunOn e.toFun cuspDomain) V (e.toFun q) =
      mfderiv halfCollarModel W.model e.toFun q (V q) := by
  have hinvq : invFunOn e.toFun cuspDomain (e.toFun q) = q :=
    e.injOn_cuspDomain.leftInvOn_invFunOn hq
  rw [VectorField.mpullback_apply]
  change (mfderiv W.model halfCollarModel (invFunOn e.toFun cuspDomain) (e.toFun q) :
        EuclideanSpace ℝ (Fin 3) →L[ℝ]
          ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))).inverse
      (V (invFunOn e.toFun cuspDomain (e.toFun q))) = _
  rw [e.mfderiv_invFunOn_inverse hq, hinvq]

/-- The pushforward by `e` of a `C¹` vector field on the cusp, as a map into the tangent bundle of
the carrier, is `C¹` (`K ≥ 1`). -/
theorem CuspEmbedding.contMDiffAt_tangent_pushforward (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    {V : (q : CuspHalfSpace) → TangentSpace halfCollarModel q}
    (hV : ContMDiffAt halfCollarModel
      (halfCollarModel.prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1))) 1
      (fun q => (⟨q, V q⟩ : TotalSpace ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) (TangentSpace halfCollarModel))) p) :
    ContMDiffAt halfCollarModel (W.model.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) 1
      (fun q => (⟨e.toFun q, mfderiv halfCollarModel W.model e.toFun q (V q)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin 3)) (TangentSpace W.model))) p := by
  have he : ContMDiffAt halfCollarModel W.model 2 e.toFun p :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).of_le
      (by exact_mod_cast Nat.add_le_add_right hK 1)
  rw [contMDiffAt_totalSpace]
  refine ⟨he.of_le one_le_two, ?_⟩
  have hVc := (contMDiffAt_totalSpace.mp hV).2
  have hc := (he.mfderiv_const (m := 1) (by norm_num)).clm_apply hVc
  refine hc.congr_of_eventuallyEq ?_
  have hbp : p ∈ (trivializationAt Ec (TangentSpace halfCollarModel) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hbe : e.toFun p ∈ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace W.model) (e.toFun p)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (e.toFun p)
  filter_upwards [(trivializationAt Ec (TangentSpace halfCollarModel) p).open_baseSet.mem_nhds hbp,
    he.continuousAt.preimage_mem_nhds
      ((trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace W.model) (e.toFun p)).open_baseSet.mem_nhds hbe)]
    with q hq hq'
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    id_eq]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hq,
    Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hq,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hq']

/-- **The pulled-back inner product of two `C¹` vector fields is `C¹`** (`K ≥ 1`). -/
theorem CuspEmbedding.contMDiffAt_pullback_inner (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    {U U' : (q : CuspHalfSpace) → TangentSpace halfCollarModel q}
    (hU : ContMDiffAt halfCollarModel
      (halfCollarModel.prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1))) 1
      (fun q => (⟨q, U q⟩ : TotalSpace ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) (TangentSpace halfCollarModel))) p)
    (hU' : ContMDiffAt halfCollarModel
      (halfCollarModel.prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1))) 1
      (fun q => (⟨q, U' q⟩ : TotalSpace ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)) (TangentSpace halfCollarModel))) p) :
    ContMDiffAt halfCollarModel 𝓘(ℝ, ℝ) 1
      (fun q => g.inner (e.toFun q) (mfderiv halfCollarModel W.model e.toFun q (U q))
        (mfderiv halfCollarModel W.model e.toFun q (U' q))) p := by
  have he : ContMDiffAt halfCollarModel W.model 2 e.toFun p :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).of_le
      (by exact_mod_cast Nat.add_le_add_right hK 1)
  have hg : ContMDiffAt halfCollarModel
      (W.model.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) 1
      (fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
        (E := fun b : W.Carrier => TangentSpace W.model b →L[ℝ] TangentSpace W.model b →L[ℝ] ℝ)
        (e.toFun q) (g.inner (e.toFun q))) p :=
    (g.contMDiff.of_le (by simp)).contMDiffAt.comp p (he.of_le one_le_two)
  have h_total := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun b : W.Carrier => TangentSpace W.model b)
    (E₂ := fun b : W.Carrier => TangentSpace W.model b)
    (E₃ := fun _ : W.Carrier => ℝ)
    (b := fun q => e.toFun q)
    (ψ := fun q => g.inner (e.toFun q))
    hg (e.contMDiffAt_tangent_pushforward hK hp hU) (e.contMDiffAt_tangent_pushforward hK hp hU')
  rw [contMDiffAt_totalSpace] at h_total
  exact h_total.2

/-- The inverse coordinate is `C²` at every point of the open collar (`K ≥ 1`). -/
theorem CuspEmbedding.contMDiffAt_invFunOn_two (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {q : CuspHalfSpace} (hq : q ∈ cuspDomain) :
    ContMDiffAt W.model halfCollarModel 2 (invFunOn e.toFun cuspDomain) (e.toFun q) :=
  (e.contMDiffOn_invFunOn_two hK).contMDiffAt
    (e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hq))

/-- The derivative of the inverse coordinate is invertible on the open collar. -/
theorem CuspEmbedding.isInvertible_mfderiv_invFunOn (e : CuspEmbedding W g K δ X)
    {q : CuspHalfSpace} (hq : q ∈ cuspDomain) :
    (mfderiv W.model halfCollarModel (invFunOn e.toFun cuspDomain) (e.toFun q)).IsInvertible := by
  obtain ⟨A₀, hA⟩ := e.isInvertible_mfderiv hq
  let A : Ec ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := A₀
  have hAL : ∀ v, A v = mfderiv halfCollarModel W.model e.toFun q v := fun v => by
    rw [← hA]
    rfl
  let Mi : EuclideanSpace ℝ (Fin 3) →L[ℝ] Ec :=
    mfderiv W.model halfCollarModel (invFunOn e.toFun cuspDomain) (e.toFun q)
  refine ⟨A.symm, ?_⟩
  refine ContinuousLinearMap.ext fun u => ?_
  have h : Mi (A (A.symm u)) = A.symm u := by
    rw [hAL]
    exact e.mfderiv_invFunOn_comp_mfderiv hq (A.symm u)
  have h2 : Mi (A (A.symm u)) = Mi u := congrArg Mi (A.apply_symm_apply u)
  exact (h.symm.trans h2)

/-- Chain rule through the inverse coordinate: `d(φ ∘ e⁻¹)(De q a) = dφ(a)`. -/
theorem CuspEmbedding.mvfderiv_comp_invFunOn (e : CuspEmbedding W g K δ X)
    {q : CuspHalfSpace} (hq : q ∈ cuspDomain) {φ : CuspHalfSpace → ℝ}
    (hφ : MDifferentiableAt halfCollarModel 𝓘(ℝ, ℝ) φ q) (a : TangentSpace halfCollarModel q) :
    mvfderiv W.model (φ ∘ invFunOn e.toFun cuspDomain) (e.toFun q)
        (mfderiv halfCollarModel W.model e.toFun q a) =
      mvfderiv halfCollarModel φ q a := by
  have heq : e.toFun q ∈ e.toFun '' cuspDomain := mem_image_of_mem _ hq
  have hinvd : MDifferentiableAt W.model halfCollarModel (invFunOn e.toFun cuspDomain)
      (e.toFun q) :=
    (e.contMDiffOn_invFunOn.contMDiffAt
      (e.isOpen_image_cuspDomain.mem_nhds heq)).mdifferentiableAt one_ne_zero
  have hed : MDifferentiableAt halfCollarModel W.model e.toFun q :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hq)).mdifferentiableAt (by simp)
  have hinvq : invFunOn e.toFun cuspDomain (e.toFun q) = q :=
    e.injOn_cuspDomain.leftInvOn_invFunOn hq
  have hφ' : MDifferentiableAt halfCollarModel 𝓘(ℝ, ℝ) φ
      (invFunOn e.toFun cuspDomain (e.toFun q)) := by
    rw [hinvq]
    exact hφ
  have hg : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (φ ∘ invFunOn e.toFun cuspDomain) (e.toFun q) :=
    hφ'.comp (e.toFun q) hinvd
  have hloc : ((φ ∘ invFunOn e.toFun cuspDomain) ∘ e.toFun) =ᶠ[𝓝 q] φ := by
    filter_upwards [isOpen_cuspDomain.mem_nhds hq] with r hr
    simp only [comp_apply, e.injOn_cuspDomain.leftInvOn_invFunOn hr]
  have h := mvfderiv_comp_apply q hg hed a
  rw [← h]
  unfold mvfderiv
  rw [hloc.mfderiv_eq, hloc.eq_of_nhds]
  rfl

end DifferentialGeometry.Geometry.Collapse
