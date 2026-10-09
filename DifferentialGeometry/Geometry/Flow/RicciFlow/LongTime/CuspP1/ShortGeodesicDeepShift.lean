import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepFun
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- The height coordinate of the half line is an immersion into `ℝ`. -/
theorem coordImmersion_CPA2 :
    IsImmersion (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun u : EuclideanHalfSpace 1 => u.val 0) := by
  refine IsImmersionOfComplement.isImmersion (F := PUnit) ?_
  intro x
  let T := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  refine IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    (contMDiff_halfSpaceOneCoordinate.continuous.continuousAt)
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) PUnit).trans T) ?_
  intro y hy
  have hyr : y ∈ range (𝓡∂ 1) := by
    have := (extChartAt_target_subset_range x) hy
    exact this
  change (extChartAt 𝓘(ℝ, ℝ) ((fun u : EuclideanHalfSpace 1 => u.val 0) x))
      ((fun u : EuclideanHalfSpace 1 => u.val 0) ((extChartAt (𝓡∂ 1) x).symm y)) =
    T ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) PUnit) (y, 0))
  simp only [extChartAt_self_apply]
  have h1 : (extChartAt (𝓡∂ 1) x).symm y = (𝓡∂ 1).symm y := rfl
  have h2 : ((𝓡∂ 1).symm y).val = y :=
    (𝓡∂ 1).right_inv hyr
  rw [h1]
  change ((𝓡∂ 1).symm y).val 0 = _
  rw [h2]
  rfl

/-- Translation of the real line as a diffeomorphism. -/
def translate_CPA2 (b : ℝ) : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := Equiv.addRight b
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

theorem shiftImmersion_CPA2 (b : ℝ) :
    IsImmersion (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun u : EuclideanHalfSpace 1 => u.val 0 + b) :=
  coordImmersion_CPA2.comp_diffeomorph (translate_CPA2 b)

theorem toYImmersion_CPA2 (b : ℝ) :
    IsImmersion halfCollarModel signedCollarModel ∞
      (fun q : CuspHalfSpace => (q.1, q.2.val 0 + b)) :=
  (IsImmersion.id (I := torusModel) (M := Torus) (n := ∞)).prodMap (shiftImmersion_CPA2 b)

theorem continuous_halfSpaceOneLift_CPA2 : Continuous halfSpaceOneLift :=
  (𝓡∂ 1).continuous_symm.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.continuous

/-- Shift of the half collar by `b` in the height direction. -/
def shift_CPA2 (b : ℝ) (q : CuspHalfSpace) : CuspHalfSpace :=
  (q.1, halfSpaceOneLift (q.2.val 0 + b))

theorem shift_height_CPA2 {b : ℝ} (hb : 0 ≤ b) (q : CuspHalfSpace) :
    (shift_CPA2 b q).2.val 0 = q.2.val 0 + b := by
  have h0 : (0 : ℝ) ≤ q.2.val 0 := q.2.2
  change max (q.2.val 0 + b) 0 = _
  exact max_eq_left (by linarith)

theorem continuous_shift_CPA2 (b : ℝ) : Continuous (shift_CPA2 b) := by
  refine continuous_fst.prodMk ?_
  have h1 : Continuous (fun q : CuspHalfSpace => q.2.val 0 + b) :=
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)).add
      continuous_const
  exact continuous_halfSpaceOneLift_CPA2.comp h1

theorem isEmbedding_shift_CPA2 {b : ℝ} (hb : 0 ≤ b) : Topology.IsEmbedding (shift_CPA2 b) := by
  let r : CuspHalfSpace → CuspHalfSpace := fun q => (q.1, halfSpaceOneLift (q.2.val 0 - b))
  have hr : Continuous r := by
    refine continuous_fst.prodMk ?_
    have h1 : Continuous (fun q : CuspHalfSpace => q.2.val 0 - b) :=
      ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)).sub
        continuous_const
    exact continuous_halfSpaceOneLift_CPA2.comp h1
  have hl : Function.LeftInverse r (shift_CPA2 b) := by
    intro q
    refine Prod.ext rfl ?_
    change halfSpaceOneLift ((shift_CPA2 b q).2.val 0 - b) = q.2
    rw [shift_height_CPA2 hb, add_sub_cancel_right]
    have h0 : (0 : ℝ) ≤ q.2.val 0 := q.2.2
    apply Subtype.ext
    ext i
    rw [Subsingleton.elim i 0]
    change max (q.2.val 0) 0 = _
    exact max_eq_left h0
  exact hl.isEmbedding hr (continuous_shift_CPA2 b)

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

/-- The `i`-th cusp parametrization pushed `b` deeper. -/
def deepCuspMap_CPA2 (b : ℝ) (i : Fin T.count) : CuspHalfSpace → H.Carrier :=
  fun q => T.cuspMap i (shift_CPA2 b q)

/-- The interior of the half collar, as a partial diffeomorphism from `T² × ℝ`. -/
def interiorLift_CPA2 :
    PartialDiffeomorph signedCollarModel halfCollarModel (Torus × ℝ) CuspHalfSpace ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.prod
    (Diffeomorph.refl torusModel Torus ∞).toPartialDiffeomorph halfSpaceOneInteriorDiffeomorph

theorem interiorLift_apply_CPA2 (y : Torus × ℝ) :
    interiorLift_CPA2 y = (y.1, halfSpaceOneLift y.2) := rfl

theorem interiorLift_source_CPA2 :
    interiorLift_CPA2.source = (univ : Set Torus) ×ˢ Ioi (0 : ℝ) := by
  have h1 : (Diffeomorph.refl torusModel Torus ∞).toPartialDiffeomorph.source = univ := rfl
  have h2 : halfSpaceOneInteriorDiffeomorph.source = Ioi (0 : ℝ) := rfl
  change (Diffeomorph.refl torusModel Torus ∞).toPartialDiffeomorph.source ×ˢ
    halfSpaceOneInteriorDiffeomorph.source = _
  rw [h1, h2]

theorem isSmoothEmbedding_deepCuspMap_CPA2 {b : ℝ} (hb : 0 < b) (i : Fin T.count) :
    IsSmoothEmbedding halfCollarModel (𝓡 3) ∞ (deepCuspMap_CPA2 T b i) := by
  refine ⟨?_, (T.cuspEmbedding i).isEmbedding.comp (isEmbedding_shift_CPA2 hb.le)⟩
  let θ : Torus × ℝ → H.Carrier := fun y => T.cuspMap i (y.1, halfSpaceOneLift y.2)
  have hθ : IsLocalDiffeomorphOn signedCollarModel (𝓡 3) ∞ θ
      (range fun q : CuspHalfSpace => (q.1, q.2.val 0 + b)) := by
    rintro ⟨y, q, rfl⟩
    have h0 : (0 : ℝ) ≤ q.2.val 0 := q.2.2
    have hy : (q.1, q.2.val 0 + b) ∈ interiorLift_CPA2.source := by
      rw [interiorLift_source_CPA2]
      exact ⟨trivial, show (0 : ℝ) < q.2.val 0 + b by linarith⟩
    have hd : interiorLift_CPA2 (q.1, q.2.val 0 + b) ∈ (cuspChart_CPA2 T i).source := by
      rw [cuspChart_source_CPA2]
      change 0 < max (q.2.val 0 + b) 0
      exact lt_max_of_lt_left (by linarith)
    have h1 := PartialDiffeomorph.isLocalDiffeomorphAt halfCollarModel (𝓡 3) ∞
      (cuspChart_CPA2 T i) hd
    have h2 := PartialDiffeomorph.isLocalDiffeomorphAt signedCollarModel halfCollarModel ∞
      interiorLift_CPA2 hy
    have h3 := IsLocalDiffeomorphAt.comp (hf := h2) (hg := h1)
    have heq : ((cuspChart_CPA2 T i : CuspHalfSpace → H.Carrier) ∘ (interiorLift_CPA2 : Torus × ℝ → CuspHalfSpace)) = θ := by
      funext z
      change (cuspChart_CPA2 T i) (z.1, halfSpaceOneLift z.2) = T.cuspMap i (z.1, halfSpaceOneLift z.2)
      exact cuspChart_apply_CPA2 T i _
    rw [heq] at h3
    exact h3
  refine DifferentialGeometry.Topology.Manifold.isImmersion_of_isImmersionAt fun q => ?_
  have hf := (toYImmersion_CPA2 b).isImmersionAt q
  have hg := hθ ⟨_, ⟨q, rfl⟩⟩
  exact hf.isLocalDiffeomorphAt_comp_of_ne_zero hg (by simp)

theorem contMDiff_halfShift_CPA2 {b : ℝ} (hb : 0 ≤ b) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (fun u : EuclideanHalfSpace 1 => halfSpaceOneLift (u.val 0 + b)) := by
  have hF : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun u : EuclideanHalfSpace 1 => u.val 0 + b) :=
    contMDiff_halfSpaceOneCoordinate.add contMDiff_const
  have := contMDiffOn_halfSpaceOneLift.comp (hF.contMDiffOn (s := univ))
    (fun u _ => show (0 : ℝ) ≤ u.val 0 + b by have : (0 : ℝ) ≤ u.val 0 := u.2; linarith)
  exact contMDiffOn_univ.mp this

/-- The differential of the half-line translation is the identity. -/
theorem mfderiv_halfShift_CPA2 {b : ℝ} (hb : 0 ≤ b) (u : EuclideanHalfSpace 1) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (fun u : EuclideanHalfSpace 1 => halfSpaceOneLift (u.val 0 + b)) u =
      ContinuousLinearMap.id ℝ _ := by
  let T := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  let g : EuclideanHalfSpace 1 → EuclideanHalfSpace 1 := fun u => halfSpaceOneLift (u.val 0 + b)
  have hg : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ g := contMDiff_halfShift_CPA2 hb
  have hgd : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) g u := (hg u).mdifferentiableAt (by simp)
  have hc := hasMFDerivAt_halfSpaceOneCoordinate (g u)
  have hcomp := hc.comp u hgd.hasMFDerivAt
  have hid : (fun u' : EuclideanHalfSpace 1 => (g u').val 0) = fun u' => u'.val 0 + b := by
    funext u'
    have h0 : (0 : ℝ) ≤ u'.val 0 := u'.2
    change max (u'.val 0 + b) 0 = _
    exact max_eq_left (by linarith)
  have h1 : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun u' : EuclideanHalfSpace 1 => u'.val 0 + b) u
      T.toContinuousLinearMap := by
    have h5 := (hasMFDerivAt_halfSpaceOneCoordinate u).add (hasMFDerivAt_const b u)
    exact h5.congr_mfderiv (add_zero _)
  have h2 : T.toContinuousLinearMap.comp (mfderiv (𝓡∂ 1) (𝓡∂ 1) g u) = T.toContinuousLinearMap := by
    have h3 : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun u' : EuclideanHalfSpace 1 => (g u').val 0) u
        (T.toContinuousLinearMap.comp (mfderiv (𝓡∂ 1) (𝓡∂ 1) g u)) := by
      have := hcomp
      exact this
    rw [hid] at h3
    exact h3.mfderiv.symm.trans h1.mfderiv
  refine ContinuousLinearMap.ext fun v => ?_
  have := congrArg (fun L => L v) h2
  exact T.injective this

theorem mfderiv_shift_CPA2 {b : ℝ} (hb : 0 ≤ b) (p : CuspHalfSpace) :
    mfderiv halfCollarModel halfCollarModel (shift_CPA2 b) p = ContinuousLinearMap.id ℝ _ := by
  have hg : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1)
      (fun u : EuclideanHalfSpace 1 => halfSpaceOneLift (u.val 0 + b)) p.2 :=
    ((contMDiff_halfShift_CPA2 hb) p.2).mdifferentiableAt (by simp)
  have := mfderiv_prodMap (p := p) (f := (id : Torus → Torus))
    (g := fun u : EuclideanHalfSpace 1 => halfSpaceOneLift (u.val 0 + b))
    (show MDifferentiableAt torusModel torusModel (id : Torus → Torus) p.1 from mdifferentiableAt_id) hg
  rw [mfderiv_id, mfderiv_halfShift_CPA2 hb] at this
  exact this

end GC.LongTime.CuspP1
