import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
# Actual retained signed seams and quotient differentials after fibre excision
-/

set_option autoImplicit false

noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)

include h3 hI in
private theorem closedFibreRemoved_not_block {x : G.cutCarrier.Carrier}
    (hx : x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})
    (j : Fin G.pairing.count) : x ∉ G.pairing.gluing.block j := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hs : p ∈ φ.source := h3 (by
    change ‖p.1.down‖ ≤ 1 at hp
    change ‖p.1.down‖ ≤ 3
    linarith)
  have hi := hI (φ.map_source hs)
  intro hb
  have hboundary : G.cutCarrier.model.IsBoundaryPoint (φ p) := by
    change φ p ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    exact Or.inl (mem_iUnion.mpr ⟨j, hb⟩)
  exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hboundary

include h3 hI in
theorem fibreClosedRemoved_saturated {x y : G.cutCarrier.Carrier}
    (h : G.pairing.gluing.rel x y) :
    (x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1}) ↔
      y ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  constructor
  · intro hx
    exact (G.pairing.gluing.eq_of_rel_of_notMem
      (G.closedFibreRemoved_not_block φ h3 hI hx) h) ▸ hx
  · intro hy
    exact (G.pairing.gluing.eq_of_rel_of_notMem
      (G.closedFibreRemoved_not_block φ h3 hI hy)
      (G.pairing.gluing.isEquivalence_rel.symm h)) ▸ hy

theorem fibreClosedAmbient_mem_iff (x : G.cutCarrier.Carrier) :
    G.reconstruction (G.pairing.quotientMap x) ∈
        (G.transportRegularFibreTube φ h3 hI) ''
          {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} ↔
      x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  rw [G.transportRegularFibreTube_closedDisc_image φ h3 hI]
  constructor
  · rintro ⟨y, hy, he⟩
    have hq : G.pairing.quotientMap y = G.pairing.quotientMap x :=
      G.reconstruction.injective he
    exact (G.fibreClosedRemoved_saturated φ h3 hI
      ((Quotient.eq' (s₁ := G.pairing.gluing.setoid)).mp hq)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)

include hδ1 in
private theorem shrunkSigned_positive (j : Fin G.pairing.count) (t : Torus)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    shrinkSignedCollar hδ (G.seam j) (t, s) =
      G.reconstruction (G.pairing.quotientMap (G.pairing.rightCollar j
        (G.pairing.matching j t, halfSpaceScale hδ (halfPoint s hs)))) := by
  rw [shrinkSignedCollar_apply, halfSpaceScale_halfPoint]
  exact G.seam_positive j t (δ * s) (mul_nonneg hδ.le hs) (by nlinarith)

include hδ1 in
private theorem shrunkSigned_negative (j : Fin G.pairing.count) (t : Torus)
    (s : ℝ) (hs : s ≤ 0) (hs1 : -1 < s) :
    shrinkSignedCollar hδ (G.seam j) (t, s) =
      G.reconstruction (G.pairing.quotientMap (G.pairing.leftCollar j
        (t, halfSpaceScale hδ (halfPoint (-s) (neg_nonneg.mpr hs))))) := by
  rw [shrinkSignedCollar_apply, halfSpaceScale_halfPoint]
  have he : halfPoint (δ * -s) (mul_nonneg hδ.le (neg_nonneg.mpr hs)) =
      halfPoint (-(δ * s)) (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hδ.le hs)) := by
    congr 1
    ring
  rw [he]
  exact G.seam_negative j t (δ * s) (mul_nonpos_of_nonneg_of_nonpos hδ.le hs)
    (by nlinarith)

variable (K : CompactCarrier.{u})
variable (O : PartialDiffeomorph G.cutCarrier.model K.model
  G.cutCarrier.Carrier K.Carrier ∞)
variable (hOs : O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hleft : ∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆ O.source)
variable (hright : ∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆ O.source)
variable (L : CompactCarrier.{u})
variable (O_L : PartialDiffeomorph W.model L.model W.Carrier L.Carrier ∞)
variable (hO_Ls : O_L.source = ((G.transportRegularFibreTube φ h3 hI) ''
  {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)

include hδ1 hOs hleft hright hO_Ls in
private theorem retainedSigned_map_source (j : Fin G.pairing.count)
    (p : Torus × ℝ) (hp : p ∈ signedCollarSource) :
    shrinkSignedCollar hδ (G.seam j) p ∈ O_L.source := by
  rw [hO_Ls]
  rcases p with ⟨t, s⟩
  change -1 < s ∧ s < 1 at hp
  by_cases hs : 0 ≤ s
  · rw [G.shrunkSigned_positive hδ hδ1 j t s hs hp.2]
    have hz : (G.pairing.matching j t, halfPoint s hs) ∈ halfCollarSource := hp.2
    have hsrc := shrinkHalfCollar_source hδ hδ1 (G.pairing.right_source j)
    have ho := hright j ((shrinkHalfCollar hδ (G.pairing.rightCollar j)).map_source
      (by rw [hsrc]; exact hz))
    rw [hOs] at ho
    exact (not_congr (G.fibreClosedAmbient_mem_iff φ h3 hI _)).mpr ho
  · have hs' : s ≤ 0 := (lt_of_not_ge hs).le
    rw [G.shrunkSigned_negative hδ hδ1 j t s hs' hp.1]
    have hz : (t, halfPoint (-s) (neg_nonneg.mpr hs')) ∈ halfCollarSource := by
      change -s < 1
      linarith
    have hsrc := shrinkHalfCollar_source hδ hδ1 (G.pairing.left_source j)
    have ho := hleft j ((shrinkHalfCollar hδ (G.pairing.leftCollar j)).map_source
      (by rw [hsrc]; exact hz))
    rw [hOs] at ho
    exact (not_congr (G.fibreClosedAmbient_mem_iff φ h3 hI _)).mpr ho

def fibreRetainedSeam (L : CompactCarrier.{u})
    (O_L : PartialDiffeomorph W.model L.model W.Carrier L.Carrier ∞)
    (hδ : 0 < δ) (j : Fin G.pairing.count) :
    PartialDiffeomorph signedCollarModel L.model (Torus × ℝ) L.Carrier ∞ :=
  (shrinkSignedCollar hδ (G.seam j)).trans O_L

include h3 hI hδ1 hOs hleft hright hO_Ls in
theorem fibreRetainedSeam_source (j : Fin G.pairing.count) :
    (G.fibreRetainedSeam L O_L hδ j).source = signedCollarSource := by
  ext p
  change (p ∈ (shrinkSignedCollar hδ (G.seam j)).source ∧
    shrinkSignedCollar hδ (G.seam j) p ∈ O_L.source) ↔ p ∈ signedCollarSource
  rw [shrinkSignedCollar_source hδ hδ1 (G.seam_source j)]
  exact ⟨And.left, fun hp => ⟨hp,
    G.retainedSigned_map_source φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls j p hp⟩⟩

theorem fibreRetainedSeam_interior (j : Fin G.pairing.count) :
    (G.fibreRetainedSeam L O_L hδ j).target ⊆ L.interior := by
  intro y hy
  have ho : y ∈ O_L.target := hy.1
  have hs : O_L.symm y ∈ (shrinkSignedCollar hδ (G.seam j)).target := hy.2
  have hi : W.model.IsInteriorPoint (O_L.symm y) :=
    G.seam_interior j (shrinkSignedCollar_target_subset hδ _ hs)
  have hloc := O_L.isLocalDiffeomorphAt W.model L.model ∞ (O_L.map_target ho)
  have h := (hloc.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp hi
  exact O_L.right_inv ho ▸ h

theorem fibreRetainedSeam_disjoint :
    Pairwise (fun i j => Disjoint (G.fibreRetainedSeam L O_L hδ i).target
      (G.fibreRetainedSeam L O_L hδ j).target) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro y hyi hyj
  exact Set.disjoint_left.mp (G.seam_disjoint hij)
    (shrinkSignedCollar_target_subset hδ _ hyi.2)
    (shrinkSignedCollar_target_subset hδ _ hyj.2)

private theorem retainedFold_smooth
    (ι : K.Carrier → G.cutCarrier.Carrier)
    (hsm : ContMDiff K.model G.cutCarrier.model ∞ ι)
    (η : L.Carrier → W.Carrier) (hη : IsSmoothEmbedding L.model W.model ∞ η)
    (f : C(K.Carrier, L.Carrier))
    (hsquare : ∀ x, η (f x) = G.reconstruction (G.pairing.quotientMap (ι x))) :
    ContMDiff K.model L.model ∞ f := by
  apply (ContMDiff.iff_comp_isImmersion hη.isImmersion).mpr
  refine ⟨f.continuous, ?_⟩
  exact (G.quotient_smooth.comp hsm).congr (fun x => hsquare x)

private theorem retainedFold_bijective_mfderiv
    (ι : K.Carrier → G.cutCarrier.Carrier)
    (hsm : ContMDiff K.model G.cutCarrier.model ∞ ι)
    (hbij : ∀ x, Bijective (mfderiv K.model G.cutCarrier.model ι x))
    (η : L.Carrier → W.Carrier) (hη : IsSmoothEmbedding L.model W.model ∞ η)
    (hηbij : ∀ x, Bijective (mfderiv L.model W.model η x))
    (f : C(K.Carrier, L.Carrier))
    (hsquare : ∀ x, η (f x) = G.reconstruction (G.pairing.quotientMap (ι x)))
    (x : K.Carrier) : Bijective (mfderiv K.model L.model f x) := by
  have hf := G.retainedFold_smooth K L ι hsm η hη f hsquare
  have heq : η ∘ f = (G.reconstruction ∘ G.pairing.quotientMap) ∘ ι := funext hsquare
  obtain ⟨D, hD, hDo⟩ := G.quotient_oriented (ι x)
  have hDb : Bijective (mfderiv G.cutCarrier.model W.model
      (G.reconstruction ∘ G.pairing.quotientMap) (ι x)) := by
    have he : (D : TangentSpace G.cutCarrier.model (ι x) →
        TangentSpace W.model (G.reconstruction (G.pairing.quotientMap (ι x)))) =
        mfderiv G.cutCarrier.model W.model
          (G.reconstruction ∘ G.pairing.quotientMap) (ι x) := funext hD
    rw [← he]
    exact D.bijective
  have hc : Bijective (mfderiv K.model W.model (η ∘ f) x) := by
    rw [heq, mfderiv_comp x
      (G.quotient_smooth.mdifferentiable (by simp) (ι x))
      (hsm.mdifferentiable (by simp) x)]
    exact hDb.comp (hbij x)
  rw [mfderiv_comp x (hη.contMDiff.mdifferentiable (by simp) (f x))
    (hf.mdifferentiable (by simp) x)] at hc
  have hc' : Bijective ((mfderiv L.model W.model η (f x)) ∘
      (mfderiv K.model L.model f x)) := hc
  exact hc'.of_comp_left (hηbij (f x)).injective

private theorem retainedOrientation_map_trans {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup H] [Module ℝ H] (A : E ≃ₗ[ℝ] F) (B : F ≃ₗ[ℝ] H)
    (o : Orientation ℝ E (Fin 3)) :
    Orientation.map (Fin 3) (A.trans B) o =
      Orientation.map (Fin 3) B (Orientation.map (Fin 3) A o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

set_option backward.isDefEq.respectTransparency false in
private theorem retainedFold_oriented
    (ι : K.Carrier → G.cutCarrier.Carrier)
    (hsm : ContMDiff K.model G.cutCarrier.model ∞ ι)
    (hbij : ∀ x, Bijective (mfderiv K.model G.cutCarrier.model ι x))
    (ho : ∀ x, Orientation.map (Fin 3)
      (Manifold.differentialEquivOfBijective K.model G.cutCarrier.model ι hbij x).toLinearEquiv
      (K.orientation.orientation x) = G.cutCarrier.orientation.orientation (ι x))
    (η : L.Carrier → W.Carrier) (hη : IsSmoothEmbedding L.model W.model ∞ η)
    (hηbij : ∀ x, Bijective (mfderiv L.model W.model η x))
    (hηor : ∀ x, Orientation.map (Fin 3)
      (Manifold.differentialEquivOfBijective L.model W.model η hηbij x).toLinearEquiv
      (L.orientation.orientation x) = W.orientation.orientation (η x))
    (f : C(K.Carrier, L.Carrier))
    (hsquare : ∀ x, η (f x) = G.reconstruction (G.pairing.quotientMap (ι x)))
    (x : K.Carrier) :
    ∃ D : TangentSpace K.model x ≃ₗ[ℝ] TangentSpace L.model (f x),
      (∀ v, D v = mfderiv K.model L.model f x v) ∧
      Orientation.map (Fin 3) D (K.orientation.orientation x) =
        L.orientation.orientation (f x) := by
  have hf := G.retainedFold_smooth K L ι hsm η hη f hsquare
  have hfbij := G.retainedFold_bijective_mfderiv K L ι hsm hbij η hη hηbij f hsquare
  let A := (Manifold.differentialEquivOfBijective K.model G.cutCarrier.model ι hbij
    x).toLinearEquiv
  let D := (Manifold.differentialEquivOfBijective K.model L.model f hfbij x).toLinearEquiv
  let B := (Manifold.differentialEquivOfBijective L.model W.model η hηbij (f x)).toLinearEquiv
  obtain ⟨R, hR, hRo⟩ := G.quotient_oriented (ι x)
  have heq : η ∘ f = (G.reconstruction ∘ G.pairing.quotientMap) ∘ ι := funext hsquare
  have hchain : A.trans R = D.trans B := by
    ext v
    change R (mfderiv K.model G.cutCarrier.model ι x v) =
      mfderiv L.model W.model η (f x) (mfderiv K.model L.model f x v)
    rw [hR]
    have hc := congrArg (fun g : K.Carrier → W.Carrier => mfderiv K.model W.model g x v) heq
    rw [mfderiv_comp x (hη.contMDiff.mdifferentiable (by simp) (f x))
      (hf.mdifferentiable (by simp) x), mfderiv_comp x
        (G.quotient_smooth.mdifferentiable (by simp) (ι x))
        (hsm.mdifferentiable (by simp) x)] at hc
    exact hc.symm
  refine ⟨D, fun v => rfl, ?_⟩
  apply (Orientation.map (Fin 3) B).injective
  rw [hηor]
  calc
    Orientation.map (Fin 3) B (Orientation.map (Fin 3) D (K.orientation.orientation x)) =
        Orientation.map (Fin 3) (D.trans B) (K.orientation.orientation x) :=
      (retainedOrientation_map_trans D B (K.orientation.orientation x)).symm
    _ = Orientation.map (Fin 3) (A.trans R) (K.orientation.orientation x) :=
      congrArg (fun e => Orientation.map (Fin 3) e (K.orientation.orientation x)) hchain.symm
    _ = Orientation.map (Fin 3) R
        (Orientation.map (Fin 3) A (K.orientation.orientation x)) :=
      retainedOrientation_map_trans A R (K.orientation.orientation x)
    _ = Orientation.map (Fin 3) R (G.cutCarrier.orientation.orientation (ι x)) :=
      congrArg (Orientation.map (Fin 3) R) (ho x)
    _ = W.orientation.orientation (η (f x)) :=
      (hsquare x).symm ▸ hRo

variable (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hrange : range ι = G.FibreCutComplement φ)
variable (hsm : ContMDiff K.model G.cutCarrier.model ∞ ι)
variable (hbij : ∀ x, Bijective (mfderiv K.model G.cutCarrier.model ι x))
variable (ho : ∀ x, Orientation.map (Fin 3)
  (Manifold.differentialEquivOfBijective K.model G.cutCarrier.model ι hbij x).toLinearEquiv
  (K.orientation.orientation x) = G.cutCarrier.orientation.orientation (ι x))
variable (hO : ∀ x, x ∈ O.source → ι (O x) = x)
variable (η : L.Carrier → W.Carrier)
variable (hη : IsSmoothEmbedding L.model W.model ∞ η)
variable (hηbij : ∀ x, Bijective (mfderiv L.model W.model η x))
variable (hηor : ∀ x, Orientation.map (Fin 3)
  (Manifold.differentialEquivOfBijective L.model W.model η hηbij x).toLinearEquiv
  (L.orientation.orientation x) = W.orientation.orientation (η x))
variable (hO_L : ∀ x, x ∈ O_L.source → η (O_L x) = x)


variable (ρ : (G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).QuotientSpace ≃ₜ L.Carrier)
variable (hρ : ∀ x : K.Carrier,
  η (ρ ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).quotientMap x)) = G.reconstruction (G.pairing.quotientMap (ι x)))

include hδ1 hOs hleft hright hO_Ls hO_L in
theorem fibreRetainedSeam_ambient (j : Fin G.pairing.count)
    (p : Torus × ℝ) (hp : p ∈ signedCollarSource) :
    η (G.fibreRetainedSeam L O_L hδ j p) = shrinkSignedCollar hδ (G.seam j) p :=
  hO_L _ (G.retainedSigned_map_source φ h3 hI hδ hδ1 K O hOs hleft hright
    L O_L hO_Ls j p hp)

include hη hOs hO_Ls hO_L hρ in
theorem fibreRetainedSeam_positive (j : Fin G.pairing.count) (t : Torus)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    G.fibreRetainedSeam L O_L hδ j (t, s) =
      ρ ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).quotientMap
        ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).rightCollar j (G.pairing.matching j t, halfPoint s hs))) := by
  apply hη.isEmbedding.injective
  have hp : (t, s) ∈ signedCollarSource := ⟨by linarith, hs1⟩
  rw [G.fibreRetainedSeam_ambient φ h3 hI hδ hδ1 K O hOs hleft hright L O_L
    hO_Ls η hO_L j (t, s) hp]
  rw [G.shrunkSigned_positive hδ hδ1 j t s hs hs1, hρ]
  rw [G.fibreRetainedPairing_rightCollar φ h3 hI K ι hι hrange hsm hbij ho O hO
    hδ hδ1 hleft hright j (G.pairing.matching j t, halfPoint s hs) hs1]

include hη hOs hO_Ls hO_L hρ in
theorem fibreRetainedSeam_negative (j : Fin G.pairing.count) (t : Torus)
    (s : ℝ) (hs : s ≤ 0) (hs1 : -1 < s) :
    G.fibreRetainedSeam L O_L hδ j (t, s) =
      ρ ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).quotientMap
        ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).leftCollar j (t, halfPoint (-s) (neg_nonneg.mpr hs)))) := by
  apply hη.isEmbedding.injective
  have hp : (t, s) ∈ signedCollarSource := ⟨hs1, by linarith⟩
  rw [G.fibreRetainedSeam_ambient φ h3 hI hδ hδ1 K O hOs hleft hright L O_L
    hO_Ls η hO_L j (t, s) hp]
  rw [G.shrunkSigned_negative hδ hδ1 j t s hs hs1, hρ]
  have hh : (t, halfPoint (-s) (neg_nonneg.mpr hs)) ∈ halfCollarSource := by
    change -s < 1
    linarith
  rw [G.fibreRetainedPairing_leftCollar φ h3 hI K ι hι hrange hsm hbij ho O hO
    hδ hδ1 hleft hright j (t, halfPoint (-s) (neg_nonneg.mpr hs)) hh]

include hη hOs hO_Ls hO_L hρ in
theorem fibreRetainedSeam_zero (j : Fin G.pairing.count) (t : Torus) :
    G.fibreRetainedSeam L O_L hδ j (t, 0) =
      ρ ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).quotientMap
        ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
      hδ hδ1 hleft hright).leftParam j t)) := by
  have hp := G.fibreRetainedSeam_negative φ h3 hI hδ hδ1 K O hOs hleft hright L O_L
    hO_Ls ι hι hrange hsm hbij ho hO η hη hO_L ρ hρ j t 0 le_rfl (by norm_num)
  have hz : halfPoint (-0) (neg_nonneg.mpr (le_refl (0 : ℝ))) = halfZero :=
    halfPoint_eq_self halfZero _ (by change -(0 : ℝ) = 0; simp)
  rw [hz] at hp
  let P := G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
    hδ hδ1 hleft hright
  have hPzero : P.leftCollar j (t, halfZero) = P.leftParam j t := P.left_zero j t
  exact hp.trans (congrArg (fun x : K.Carrier => ρ (P.quotientMap x)) hPzero)

include hη hρ in
theorem fibreRetainedFold_contMDiff :
    ContMDiff K.model L.model ∞ (ρ ∘
      (G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
        hδ hδ1 hleft hright).quotientMap) := by
  let P := G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
    hδ hδ1 hleft hright
  let f : C(K.Carrier, L.Carrier) :=
    ⟨ρ ∘ P.quotientMap, ρ.continuous.comp P.quotientMap.continuous⟩
  exact G.retainedFold_smooth K L ι hsm η hη f hρ

include hη hηbij hρ in
theorem fibreRetainedFold_bijective_mfderiv (x : K.Carrier) :
    Bijective (mfderiv K.model L.model (ρ ∘
      (G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
        hδ hδ1 hleft hright).quotientMap) x) := by
  let P := G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
    hδ hδ1 hleft hright
  let f : C(K.Carrier, L.Carrier) :=
    ⟨ρ ∘ P.quotientMap, ρ.continuous.comp P.quotientMap.continuous⟩
  exact G.retainedFold_bijective_mfderiv K L ι hsm hbij η hη hηbij f hρ x

include hη hηbij hηor hρ in
theorem fibreRetainedFold_oriented (x : K.Carrier) :
    ∃ D : TangentSpace K.model x ≃ₗ[ℝ] TangentSpace L.model
        (ρ ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
          hδ hδ1 hleft hright).quotientMap x)),
      (∀ v, D v = mfderiv K.model L.model (ρ ∘
        (G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
          hδ hδ1 hleft hright).quotientMap) x v) ∧
      Orientation.map (Fin 3) D (K.orientation.orientation x) =
        L.orientation.orientation (ρ
          ((G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
            hδ hδ1 hleft hright).quotientMap x)) := by
  let P := G.fibreRetainedPairing φ h3 hI K ι hι hrange hsm hbij ho O hO
    hδ hδ1 hleft hright
  let f : C(K.Carrier, L.Carrier) :=
    ⟨ρ ∘ P.quotientMap, ρ.continuous.comp P.quotientMap.continuous⟩
  exact G.retainedFold_oriented K L ι hsm hbij ho η hη hηbij hηor f hρ x

include h3 hI in
private theorem radiusTwoFibreRemoved_not_block {x : G.cutCarrier.Carrier}
    (hx : x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})
    (j : Fin G.pairing.count) : x ∉ G.pairing.gluing.block j := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hs : p ∈ φ.source := h3 (by
    change ‖p.1.down‖ ≤ 2 at hp
    change ‖p.1.down‖ ≤ 3
    linarith)
  have hi := hI (φ.map_source hs)
  intro hb
  have hboundary : G.cutCarrier.model.IsBoundaryPoint (φ p) := by
    change φ p ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    exact Or.inl (mem_iUnion.mpr ⟨j, hb⟩)
  exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hboundary

include h3 hI in
theorem fibreRadiusTwoRemoved_saturated {x y : G.cutCarrier.Carrier}
    (h : G.pairing.gluing.rel x y) :
    (x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2}) ↔
      y ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
  constructor
  · intro hx
    exact (G.pairing.gluing.eq_of_rel_of_notMem
      (G.radiusTwoFibreRemoved_not_block φ h3 hI hx) h) ▸ hx
  · intro hy
    exact (G.pairing.gluing.eq_of_rel_of_notMem
      (G.radiusTwoFibreRemoved_not_block φ h3 hI hy)
      (G.pairing.gluing.isEquivalence_rel.symm h)) ▸ hy

theorem fibreRadiusTwoAmbient_mem_iff (x : G.cutCarrier.Carrier) :
    G.reconstruction (G.pairing.quotientMap x) ∈
        (G.transportRegularFibreTube φ h3 hI) ''
          {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} ↔
      x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
  rw [G.transportRegularFibreTube_image φ h3 hI {p | ‖p.1.down‖ ≤ 2}
    (fun p hp => h3 (by change ‖p.1.down‖ ≤ 3; exact le_trans hp (by norm_num)))]
  constructor
  · rintro ⟨y, hy, he⟩
    have hq : G.pairing.quotientMap y = G.pairing.quotientMap x :=
      G.reconstruction.injective he
    exact (G.fibreRadiusTwoRemoved_saturated φ h3 hI
      ((Quotient.eq' (s₁ := G.pairing.gluing.setoid)).mp hq)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable (haL : ∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆
  (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
variable (haR : ∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆
  (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)

include hδ1 haL haR in
private theorem shrunkSigned_avoids_radiusTwo (j : Fin G.pairing.count)
    (p : Torus × ℝ) (hp : p ∈ signedCollarSource) :
    shrinkSignedCollar hδ (G.seam j) p ∉
      (G.transportRegularFibreTube φ h3 hI) ''
        {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
  rcases p with ⟨t, s⟩
  change -1 < s ∧ s < 1 at hp
  by_cases hs : 0 ≤ s
  · rw [G.shrunkSigned_positive hδ hδ1 j t s hs hp.2]
    have hz : (G.pairing.matching j t, halfPoint s hs) ∈ halfCollarSource := hp.2
    have hsrc := shrinkHalfCollar_source hδ hδ1 (G.pairing.right_source j)
    have ha := haR j ((shrinkHalfCollar hδ (G.pairing.rightCollar j)).map_source
      (by rw [hsrc]; exact hz))
    exact (not_congr (G.fibreRadiusTwoAmbient_mem_iff φ h3 hI _)).mpr ha
  · have hs' : s ≤ 0 := (lt_of_not_ge hs).le
    rw [G.shrunkSigned_negative hδ hδ1 j t s hs' hp.1]
    have hz : (t, halfPoint (-s) (neg_nonneg.mpr hs')) ∈ halfCollarSource := by
      change -s < 1
      linarith
    have hsrc := shrinkHalfCollar_source hδ hδ1 (G.pairing.left_source j)
    have ha := haL j ((shrinkHalfCollar hδ (G.pairing.leftCollar j)).map_source
      (by rw [hsrc]; exact hz))
    exact (not_congr (G.fibreRadiusTwoAmbient_mem_iff φ h3 hI _)).mpr ha

include hδ1 hOs hleft hright hO_Ls hO_L haL haR in
theorem fibreRetainedSeam_disjoint_radial
    (Γ : PartialDiffeomorph halfCollarModel L.model
      (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource)
    (hΓ : ∀ p, p ∈ halfCollarSource →
      η (Γ p) = (G.transportRegularFibreTube φ h3 hI)
        (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (j : Fin G.pairing.count) :
    Disjoint (G.fibreRetainedSeam L O_L hδ j).target Γ.target := by
  apply Set.disjoint_left.mpr
  intro y hyS hyΓ
  let S := G.fibreRetainedSeam L O_L hδ j
  have hs : S.symm y ∈ signedCollarSource := by
    have h := S.map_target hyS
    rw [G.fibreRetainedSeam_source φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls j] at h
    exact h
  have he := G.fibreRetainedSeam_ambient φ h3 hI hδ hδ1 K O hOs hleft hright
    L O_L hO_Ls η hO_L j (S.symm y) hs
  have he := (congrArg η (S.right_inv hyS)).symm.trans he
  have hΓp : Γ.symm y ∈ halfCollarSource := hΓs ▸ Γ.map_target hyΓ
  have hΓe := hΓ (Γ.symm y) hΓp
  have hΓe := (congrArg η (Γ.right_inv hyΓ)).symm.trans hΓe
  have hm : η y ∈ (G.transportRegularFibreTube φ h3 hI) ''
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
    refine ⟨(ULift.up ((1 + (Γ.symm y).2.val 0 / 2) •
      ((Γ.symm y).1.1 : ℂ)), (Γ.symm y).1.2), ?_, hΓe.symm⟩
    change ‖(1 + (Γ.symm y).2.val 0 / 2) • ((Γ.symm y).1.1 : ℂ)‖ ≤ 2
    have hn := (Γ.symm y).2.property
    change (Γ.symm y).2.val 0 < 1 at hΓp
    rw [norm_smul, Real.norm_of_nonneg (by linarith), Circle.norm_coe, mul_one]
    linarith
  exact G.shrunkSigned_avoids_radiusTwo φ h3 hI hδ hδ1 haL haR j (S.symm y) hs (he ▸ hm)

end GC.GraphManifold.RawGraphPresentation
