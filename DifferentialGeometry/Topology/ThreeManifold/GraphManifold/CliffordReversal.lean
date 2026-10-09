import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordGluing

/-!
# The Clifford torus pairing reverses boundary orientation

We put the half collars of the two boundary tori of the disjoint union of two solid tori into the
form required by a torus pairing, and prove that the two collars induce opposite boundary
orientations from the orientation pulled back from the three-sphere. The proof writes both
collars, after folding into the sphere, through the signed Clifford collar: one through the
reflection `s ↦ -s` and one directly, so the comparison map is conjugate to that reflection.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold
universe u

theorem orientation_map_symm_eq_neg_of_det_neg {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {n : ℕ} (hV : Fintype.card (Fin n) = Module.finrank ℝ V)
    (A B : V ≃ₗ[ℝ] W) (o : Orientation ℝ W (Fin n))
    (h : LinearMap.det ((A.trans B.symm : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) < 0) :
    Orientation.map (Fin n) A.symm o = -Orientation.map (Fin n) B.symm o := by
  have hA : A.symm = B.symm.trans (A.trans B.symm).symm := by
    ext w
    simp
  rw [hA, DifferentialGeometry.orientation_map_trans, Orientation.map_eq_neg_iff_det_neg _ _ hV,
    LinearEquiv.det_coe_symm]
  exact inv_lt_zero.mpr h

theorem det_trans_symm_eq_det {V T W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup T]
    [Module ℝ T] [AddCommGroup W] [Module ℝ W] (A B : V ≃ₗ[ℝ] W) (J : V ≃ₗ[ℝ] T)
    (P : T →ₗ[ℝ] T) (S : T →ₗ[ℝ] W) (hA : ∀ v, A v = S (P (J v))) (hB : ∀ v, B v = S (J v)) :
    LinearMap.det ((A.trans B.symm : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) = LinearMap.det P := by
  have heq : ((A.trans B.symm : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) =
      ((J.symm : T ≃ₗ[ℝ] V) : T →ₗ[ℝ] V) ∘ₗ P ∘ₗ ((J.symm.symm : V ≃ₗ[ℝ] T) : V →ₗ[ℝ] T) := by
    ext v
    apply B.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearMap.comp_apply, LinearEquiv.symm_symm]
    rw [hA, hB, LinearEquiv.apply_symm_apply]
  rw [heq, LinearMap.det_conj]

theorem det_prodMap_id_neg (E : Type*) [AddCommGroup E] [Module ℝ E] [Module.Free ℝ E]
    [Module.Finite ℝ E] :
    LinearMap.det ((LinearMap.id : E →ₗ[ℝ] E).prodMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)) = -1 := by
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, ← neg_one_smul ℝ LinearMap.id,
    LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]

def seamReflection (y : Torus × ℝ) : Torus × ℝ := (y.1, -y.2)

theorem contMDiff_seamReflection :
    ContMDiff signedCollarModel signedCollarModel ∞ seamReflection :=
  contMDiff_fst.prodMk contMDiff_snd.neg

theorem mfderiv_neg_real_apply (x w : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => -y) x w = -w := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun y : ℝ => -y) x w = -w
  have h : HasFDerivAt (fun y : ℝ => -y) (-ContinuousLinearMap.id ℝ ℝ) x := (hasFDerivAt_id x).neg
  rw [h.fderiv]
  rfl

theorem mfderiv_seamReflection_apply (y : Torus × ℝ) (w : TangentSpace signedCollarModel y) :
    mfderiv signedCollarModel signedCollarModel seamReflection y w = (w.1, -w.2) := by
  have h : seamReflection = Prod.map id (fun s : ℝ => -s) := rfl
  rw [h, mfderiv_prodMap mdifferentiableAt_id
    ((contDiff_neg.contMDiff (n := ∞)).mdifferentiableAt (by simp))]
  change (mfderiv torusModel torusModel id y.1 w.1,
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s) y.2 w.2) = (w.1, -w.2)
  rw [mfderiv_id, mfderiv_neg_real_apply]
  rfl

def halfCollarHeight (q : Torus × EuclideanHalfSpace 1) : Torus × ℝ := (q.1, q.2.val 0)

theorem contMDiff_halfCollarHeight :
    ContMDiff halfCollarModel signedCollarModel ∞ halfCollarHeight :=
  contMDiff_fst.prodMk (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)

def partialDiffeomorphSumInl {E H M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M'] [Nonempty M] :
    PartialDiffeomorph I I M (M ⊕ M') ∞ where
  toFun := Sum.inl
  invFun := Sum.elim id (fun _ => Classical.arbitrary M)
  source := univ
  target := range Sum.inl
  map_source' x _ := mem_range_self x
  map_target' _ _ := mem_univ _
  left_inv' _ _ := rfl
  right_inv' := by
    rintro _ ⟨x, rfl⟩
    rfl
  open_source := isOpen_univ
  open_target := isOpen_range_inl
  contMDiffOn_toFun := ContMDiff.inl.contMDiffOn
  contMDiffOn_invFun := (ContMDiff.sumElim contMDiff_id contMDiff_const).contMDiffOn

def partialDiffeomorphSumInr {E H M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M'] [Nonempty M'] :
    PartialDiffeomorph I I M' (M ⊕ M') ∞ where
  toFun := Sum.inr
  invFun := Sum.elim (fun _ => Classical.arbitrary M') id
  source := univ
  target := range Sum.inr
  map_source' x _ := mem_range_self x
  map_target' _ _ := mem_univ _
  left_inv' _ _ := rfl
  right_inv' := by
    rintro _ ⟨x, rfl⟩
    rfl
  open_source := isOpen_univ
  open_target := isOpen_range_inr
  contMDiffOn_toFun := ContMDiff.inr.contMDiffOn
  contMDiffOn_invFun := (ContMDiff.sumElim contMDiff_const contMDiff_id).contMDiffOn

instance : Nonempty solidTorusSet.{u} := ⟨cliffordTorusPoint 1⟩

def cliffordLeftCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) CliffordCut.{u} ∞ :=
  solidTorusCollar.trans partialDiffeomorphSumInl

def cliffordRightCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) CliffordCut.{u} ∞ :=
  solidTorusCollar.trans partialDiffeomorphSumInr

theorem cliffordLeftCollar_apply (q : Torus × EuclideanHalfSpace 1) :
    cliffordLeftCollar.{u} q = Sum.inl (solidTorusCollar q) := rfl

theorem cliffordRightCollar_apply (q : Torus × EuclideanHalfSpace 1) :
    cliffordRightCollar.{u} q = Sum.inr (solidTorusCollar q) := rfl

theorem cliffordLeftCollar_source : cliffordLeftCollar.{u}.source = halfCollarSource := by
  change solidTorusCollar.{u}.source ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  rfl

theorem cliffordRightCollar_source : cliffordRightCollar.{u}.source = halfCollarSource := by
  change solidTorusCollar.{u}.source ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  rfl

theorem sphereSwap_cliffordSeamMap_swap (t : Torus) {s : ℝ} (h₁ : -1 ≤ s) (h₂ : s ≤ 1) :
    sphereSwap (cliffordSeamMap.{u} (t.swap, -s)) = cliffordSeamMap (t, s) := by
  have hs : seamClamp s = s := seamClamp_of_mem h₁ h₂
  have hs' : seamClamp (-s) = -s := seamClamp_of_mem (by linarith) (by linarith)
  apply sphere_ext
  · rw [sphereFirst_sphereSwap, sphereSecond_cliffordSeamMap, sphereFirst_cliffordSeamMap]
    change seamSecond (-s) • (t.1 : ℂ) = seamFirst s • (t.1 : ℂ)
    rw [seamSecond, seamFirst, hs, hs', sub_neg_eq_add]
  · rw [sphereSecond_sphereSwap, sphereFirst_cliffordSeamMap, sphereSecond_cliffordSeamMap]
    change seamFirst (-s) • (t.2 : ℂ) = seamSecond s • (t.2 : ℂ)
    rw [seamSecond, seamFirst, hs, hs', ← sub_eq_add_neg]

def cliffordRightCollarSwapped :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) CliffordCut.{u} ∞ :=
  (cliffordMatching.prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
    cliffordRightCollar

theorem cliffordRightCollarSwapped_apply (q : Torus × EuclideanHalfSpace 1) :
    cliffordRightCollarSwapped.{u} q = cliffordRightCollar (cliffordMatching q.1, q.2) := rfl

theorem cliffordFold_cliffordLeftCollar :
    cliffordFold ∘ cliffordLeftCollar.{u} = cliffordSeam ∘ seamReflection ∘ halfCollarHeight :=
  rfl

theorem cliffordFold_cliffordRightCollarSwapped_eventuallyEq (t : Torus) :
    cliffordFold ∘ cliffordRightCollarSwapped.{u} =ᶠ[𝓝 (t, halfZero)]
      cliffordSeam ∘ halfCollarHeight := by
  have hopen : IsOpen halfCollarSource := by
    rw [← cliffordLeftCollar_source.{u}]
    exact cliffordLeftCollar.open_source
  filter_upwards [hopen.mem_nhds (halfZero_mem_halfCollarSource t)] with q hq
  have hq' : q.2.val 0 < 1 := hq
  have h0 : 0 ≤ q.2.val 0 := q.2.2
  change sphereSwap (cliffordSeamMap ((cliffordMatching q.1), -q.2.val 0)) =
    cliffordSeamMap (q.1, q.2.val 0)
  rw [cliffordMatching_apply]
  exact sphereSwap_cliffordSeamMap_swap q.1 (by linarith) hq'.le

theorem finrank_halfCollarTangent (q : Torus × EuclideanHalfSpace 1) :
    Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace halfCollarModel q) := by
  change 3 = Module.finrank ℝ
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
  rw [Module.finrank_prod, Module.finrank_prod, finrank_euclideanSpace_fin]

theorem halfCollarHeight_mem_cliffordSeam_source (t : Torus) :
    halfCollarHeight (t, halfZero) ∈ cliffordSeam.{u}.source := by
  change -1 < halfZero.val 0 ∧ halfZero.val 0 < 1
  rw [show halfZero.val 0 = 0 from rfl]
  norm_num

theorem seamReflection_halfCollarHeight_zero (t : Torus) :
    seamReflection (halfCollarHeight (t, halfZero)) = halfCollarHeight (t, halfZero) := by
  change (t, -halfZero.val 0) = (t, halfZero.val 0)
  rw [show halfZero.val 0 = 0 from rfl, neg_zero]

theorem mfderiv_cliffordSeam_congr (y₁ y₂ : Torus × ℝ) (h : y₁ = y₂)
    (w : TangentSpace signedCollarModel y₁) :
    mfderiv signedCollarModel (𝓡 3) cliffordSeam.{u} y₁ w =
      mfderiv signedCollarModel (𝓡 3) cliffordSeam.{u} y₂ w := by
  subst h
  rfl

theorem mfderiv_cliffordFold_leftCollar_apply (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv (𝓡∂ 3) (𝓡 3) cliffordFold (cliffordLeftCollar.{u} (t, halfZero))
      (mfderiv halfCollarModel (𝓡∂ 3) cliffordLeftCollar.{u} (t, halfZero) v) =
      mfderiv signedCollarModel (𝓡 3) cliffordSeam.{u} (halfCollarHeight (t, halfZero))
        (mfderiv signedCollarModel signedCollarModel seamReflection (halfCollarHeight (t, halfZero))
          (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v)) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈ cliffordLeftCollar.{u}.source := by
    rw [cliffordLeftCollar_source]
    exact halfZero_mem_halfCollarSource t
  have hy0 := halfCollarHeight_mem_cliffordSeam_source.{u} t
  have hfold : MDifferentiableAt (𝓡∂ 3) (𝓡 3) cliffordFold (cliffordLeftCollar.{u} (t, halfZero)) :=
    contMDiff_cliffordFold.mdifferentiableAt (by simp)
  have hl : MDifferentiableAt halfCollarModel (𝓡∂ 3) cliffordLeftCollar.{u} (t, halfZero) :=
    cliffordLeftCollar.mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hρ : MDifferentiableAt signedCollarModel signedCollarModel seamReflection
      (halfCollarHeight (t, halfZero)) :=
    contMDiff_seamReflection.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel (𝓡 3) cliffordSeam.{u}
      (seamReflection (halfCollarHeight (t, halfZero))) := by
    rw [seamReflection_halfCollarHeight_zero]
    exact cliffordSeam.mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hl) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS (hρ.comp (t, halfZero) hj)) v
  have e3 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hρ hj) v
  rw [cliffordFold_cliffordLeftCollar] at e1
  exact ((e1.symm.trans e2).trans (congrArg (mfderiv signedCollarModel (𝓡 3) cliffordSeam
    (seamReflection (halfCollarHeight (t, halfZero)))) e3)).trans
      (mfderiv_cliffordSeam_congr _ _ (seamReflection_halfCollarHeight_zero t) _)

theorem mfderiv_cliffordFold_rightCollar_apply (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv (𝓡∂ 3) (𝓡 3) cliffordFold (cliffordRightCollarSwapped.{u} (t, halfZero))
      (mfderiv halfCollarModel (𝓡∂ 3) cliffordRightCollarSwapped.{u} (t, halfZero) v) =
      mfderiv signedCollarModel (𝓡 3) cliffordSeam.{u} (halfCollarHeight (t, halfZero))
        (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈
      cliffordRightCollarSwapped.{u}.source := by
    refine ⟨mem_univ _, ?_⟩
    change (cliffordMatching t, halfZero) ∈ cliffordRightCollar.{u}.source
    rw [cliffordRightCollar_source]
    exact halfZero_mem_halfCollarSource _
  have hy0 := halfCollarHeight_mem_cliffordSeam_source.{u} t
  have hfold : MDifferentiableAt (𝓡∂ 3) (𝓡 3) cliffordFold
      (cliffordRightCollarSwapped.{u} (t, halfZero)) :=
    contMDiff_cliffordFold.mdifferentiableAt (by simp)
  have hr : MDifferentiableAt halfCollarModel (𝓡∂ 3) cliffordRightCollarSwapped.{u}
      (t, halfZero) :=
    cliffordRightCollarSwapped.mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel (𝓡 3) cliffordSeam.{u}
      (halfCollarHeight (t, halfZero)) :=
    cliffordSeam.mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hr) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS hj) v
  have e4 := DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel)
    (I' := 𝓡 3) (cliffordFold_cliffordRightCollarSwapped_eventuallyEq.{u} t)) v
  exact (e1.symm.trans e4).trans e2

theorem cliffordReversing :
    ReversesBoundaryOrientation cliffordCutCarrier.{u} cliffordLeftCollar
      (fun p => cliffordRightCollar (cliffordMatching p.1, p.2)) := by
  intro t
  let q0 : Torus × EuclideanHalfSpace 1 := (t, halfZero)
  have hq0l : q0 ∈ cliffordLeftCollar.{u}.source := by
    rw [cliffordLeftCollar_source]
    exact halfZero_mem_halfCollarSource t
  have hq0r : q0 ∈ cliffordRightCollarSwapped.{u}.source := by
    refine ⟨mem_univ _, ?_⟩
    change (cliffordMatching t, halfZero) ∈ cliffordRightCollar.{u}.source
    rw [cliffordRightCollar_source]
    exact halfZero_mem_halfCollarSource _
  have hl := cliffordLeftCollar.{u}.isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hq0l
  have hr := cliffordRightCollarSwapped.{u}.isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hq0r
  let L := (hl.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let R := (hr.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  let D : (x : CliffordCut.{u}) → EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun x => (Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) cliffordFold
      mfderiv_cliffordFold_bijective x).toLinearEquiv
  have hO : ∀ x : CliffordCut.{u}, cliffordCutOrientation.orientation x =
      Orientation.map (Fin 3) (D x).symm
        (standardThreeSphereLift.{u}.orientation.orientation (cliffordFold x)) := by
    intro x
    rw [← orientation_map_cliffordCutOrientation x]
    exact (Equiv.symm_apply_apply (Orientation.map (Fin 3) (D x)) _).symm
  let y0 : Torus × ℝ := halfCollarHeight q0
  have hS := cliffordSeam.{u}.isLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞
    (halfCollarHeight_mem_cliffordSeam_source.{u} t)
  let dS := (hS.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let A := L.trans (D (cliffordLeftCollar q0))
  let B := R.trans (D (cliffordRightCollarSwapped q0))
  let J := B.trans dS.symm
  let P : (TangentSpace signedCollarModel y0) →ₗ[ℝ] (TangentSpace signedCollarModel y0) :=
    (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _).prodMap
      (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hJ : ∀ v, J v = mfderiv halfCollarModel signedCollarModel halfCollarHeight q0 v := by
    intro v
    apply dS.injective
    exact (dS.apply_symm_apply (B v)).trans (mfderiv_cliffordFold_rightCollar_apply t v)
  have hdet : LinearMap.det ((A.trans B.symm : _ ≃ₗ[ℝ] _) :
      TangentSpace halfCollarModel q0 →ₗ[ℝ] TangentSpace halfCollarModel q0) < 0 := by
    let Sₗ : TangentSpace signedCollarModel y0 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := dS.toLinearMap
    rw [det_trans_symm_eq_det A B J P Sₗ]
    · rw [show LinearMap.det P = -1 from
        det_prodMap_id_neg (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))]
      norm_num
    · intro v
      change D (cliffordLeftCollar q0) (L v) = Sₗ (P (J v))
      rw [hJ]
      exact (mfderiv_cliffordFold_leftCollar_apply t v).trans
        (congrArg Sₗ (mfderiv_seamReflection_apply _ _))
    · intro v
      change D (cliffordRightCollarSwapped q0) (R v) = Sₗ (J v)
      rw [hJ]
      exact mfderiv_cliffordFold_rightCollar_apply t v
  have hpt : cliffordFold (cliffordRightCollarSwapped.{u} q0) =
      cliffordFold (cliffordLeftCollar.{u} q0) := by
    change sphereSwap (cliffordTorusPoint (cliffordMatching t)).val =
      (cliffordTorusPoint t).val
    rw [sphereSwap_cliffordTorusPoint, cliffordMatching_apply, Prod.swap_swap]
  have hOS : ∀ p₁ p₂ : SphereCarrier.{u}, p₁ = p₂ →
      standardThreeSphereLift.{u}.orientation.orientation p₁ =
        standardThreeSphereLift.{u}.orientation.orientation p₂ := by
    rintro _ _ rfl
    rfl
  change Orientation.map (Fin 3) L.symm (cliffordCutOrientation.orientation (cliffordLeftCollar q0))
    = -Orientation.map (Fin 3) R.symm
      (cliffordCutOrientation.orientation (cliffordRightCollarSwapped q0))
  rw [hO, hO, hOS _ _ hpt]
  let o := standardThreeSphereLift.{u}.orientation.orientation
    (cliffordFold (cliffordLeftCollar q0))
  have key := orientation_map_symm_eq_neg_of_det_neg (finrank_halfCollarTangent q0) A B o hdet
  have hA' : A.symm = (D (cliffordLeftCollar q0)).symm.trans L.symm :=
    LinearEquiv.ext fun _ => rfl
  have hB' : B.symm = (D (cliffordRightCollarSwapped q0)).symm.trans R.symm :=
    LinearEquiv.ext fun _ => rfl
  rw [hA', hB'] at key
  exact (DifferentialGeometry.orientation_map_trans (D (cliffordLeftCollar q0)).symm L.symm
    o).symm.trans (key.trans (congrArg Neg.neg (DifferentialGeometry.orientation_map_trans
      (D (cliffordRightCollarSwapped q0)).symm R.symm o)))

end GC.GraphManifold
