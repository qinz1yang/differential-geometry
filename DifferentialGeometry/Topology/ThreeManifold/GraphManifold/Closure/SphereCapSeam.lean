import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapBallCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapOffBoundary

/-!
Full signed sphere seams in the actual quotient attaching tagged real balls to spherical faces.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

local instance sphereCapSeamBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance sphereCapSeamBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

private theorem sphereCapHalfLift_continuous : Continuous halfSpaceOneLift := by
  have he : halfSpaceOneLift = fun t : ℝ =>
      halfSpaceOneHomeomorph.symm ⟨max 0 t, le_max_left 0 t⟩ :=
    funext halfSpaceOneLift_eq
  rw [he]
  exact halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk (fun t => le_max_left 0 t))

private theorem sphereCapHalfLift_zero : halfSpaceOneLift 0 = halfZero :=
  (halfSpaceOneLift_coord halfZero).trans rfl

private theorem sphereCapHalfLift_halfPoint (s : ℝ) (hs : 0 ≤ s) :
    halfSpaceOneLift s = halfPoint s hs :=
  (halfPoint_eq_self (halfSpaceOneLift s) hs (max_eq_left hs).symm).symm

private theorem sphereCapHalfLift_nonpos {s : ℝ} (h : halfSpaceOneLift s = halfZero) : s ≤ 0 := by
  have hc := congrArg (fun p : EuclideanHalfSpace 1 => p.val 0) h
  change max s 0 = 0 at hc
  exact (le_max_left s 0).trans hc.le

def sphereCapSignedDomain : Opens (ClosureSphere.{u} × ℝ) :=
  ⟨sphereSignedCollarSource, isOpen_univ.prod isOpen_Ioo⟩

def sphereCapSeamMap (i : Fin B.sphereCount) (p : sphereCapSignedDomain.{u}) :
    B.SphereCapQuotient :=
  if 0 ≤ p.val.2 then B.sphereCapCore (B.sphere i (p.val.1, halfSpaceOneLift p.val.2))
  else B.sphereCapBall i (sphereCapBallCollar (p.val.1, halfSpaceOneLift (-p.val.2)))

theorem sphereCapSeamMap_zero (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.sphereCapSeamMap i ⟨(z, 0), by constructor <;> norm_num⟩ =
      B.sphereCapCore (B.sphereMap i z) := by
  simp only [sphereCapSeamMap, le_refl, ↓reduceIte, sphereCapHalfLift_zero]
  rfl

private theorem sphereCapSeam_core_source (i : Fin B.sphereCount)
    (p : sphereCapSignedDomain.{u}) :
    (p.val.1, halfSpaceOneLift p.val.2) ∈ (B.sphere i).source := by
  rw [B.sphere_source]
  change max p.val.2 0 < 1
  exact max_lt p.property.2.2 zero_lt_one

private theorem sphereCapSeam_ball_source (p : sphereCapSignedDomain.{u}) :
    (p.val.1, halfSpaceOneLift (-p.val.2)) ∈ sphereCapBallCollar.source := by
  rw [sphereCapBallCollar_source]
  change max (-p.val.2) 0 < 1
  exact max_lt (by linarith [p.property.2.1]) zero_lt_one

theorem sphereCapSeamMap_continuous (i : Fin B.sphereCount) :
    Continuous (B.sphereCapSeamMap i) := by
  have hs : Continuous (fun p : sphereCapSignedDomain.{u} => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hz : Continuous (fun p : sphereCapSignedDomain.{u} => p.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have hc : Continuous (fun p : sphereCapSignedDomain.{u} =>
      B.sphereCapCore (B.sphere i (p.val.1, halfSpaceOneLift p.val.2))) :=
    B.sphereCapCore.continuous.comp
      ((B.sphere i).toOpenPartialHomeomorph.continuousOn.comp_continuous
      (hz.prodMk (sphereCapHalfLift_continuous.comp hs)) (B.sphereCapSeam_core_source i))
  have hb : Continuous (fun p : sphereCapSignedDomain.{u} =>
      B.sphereCapBall i (sphereCapBallCollar (p.val.1, halfSpaceOneLift (-p.val.2)))) :=
    (B.sphereCapBall i).continuous.comp
      (sphereCapBallCollar.toOpenPartialHomeomorph.continuousOn.comp_continuous
      (hz.prodMk (sphereCapHalfLift_continuous.comp hs.neg)) sphereCapSeam_ball_source)
  apply Continuous.if ?_ hc hb
  intro p hp
  have hbd := hs.frontier_preimage_subset (Ici (0 : ℝ)) hp
  have hzero : p.val.2 = 0 := by
    simpa only [mem_preimage, frontier_Ici, mem_singleton_iff, Function.comp_apply] using hbd
  rw [hzero, neg_zero, sphereCapHalfLift_zero, sphereCapBallCollar_zero]
  exact B.sphereCap_attachment i p.val.1

private theorem sphereCapSeam_cross (i : Fin B.sphereCount)
    {p q : ClosureSphere.{u} × EuclideanHalfSpace 1}
    (hp : p ∈ (B.sphere i).source) (hq : q ∈ sphereCapBallCollar.source)
    (h : B.sphereCapCore (B.sphere i p) = B.sphereCapBall i (sphereCapBallCollar q)) :
    p = q ∧ p.2 = halfZero := by
  have hr := (B.sphereCapGluing_rel_iff _ _).mp (Quotient.exact h)
  rcases hr with he | ⟨j, z, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · cases he
  · have hij : i = j := congrArg Prod.fst (Sum.inr_injective hy)
    subst j
    have hz : (z, halfZero) ∈ (B.sphere i).source := by
      rw [B.sphere_source]
      change (0 : ℝ) < 1
      exact zero_lt_one
    have hpz : p = (z, halfZero) := (B.sphere i).injOn hp hz (Sum.inl_injective hx)
    have hz' : (z, halfZero) ∈ sphereCapBallCollar.source := by
      rw [sphereCapBallCollar_source]
      change (0 : ℝ) < 1
      exact zero_lt_one
    have he : sphereCapBallCollar q = sphereCapBallCollar (z, halfZero) :=
      (congrArg Prod.snd (Sum.inr_injective hy)).trans (sphereCapBallCollar_zero z).symm
    have hqz : q = (z, halfZero) := sphereCapBallCollar.injOn hq hz' he
    exact ⟨hpz.trans hqz.symm, congrArg Prod.snd hpz⟩
  · dsimp [sphereCapRight] at hx
    cases hx

theorem sphereCapSeamMap_injective (i : Fin B.sphereCount) :
    Injective (B.sphereCapSeamMap i) := by
  intro p q he
  by_cases hp : 0 ≤ p.val.2
  · by_cases hq : 0 ≤ q.val.2
    · simp only [sphereCapSeamMap, hp, hq, ↓reduceIte] at he
      have h := (B.sphere i).injOn (B.sphereCapSeam_core_source i p)
        (B.sphereCapSeam_core_source i q) (B.sphereCapCore_injective he)
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun v : ClosureSphere.{u} × EuclideanHalfSpace 1 => v.1) h
      · have hc := congrArg (fun v : ClosureSphere.{u} × EuclideanHalfSpace 1 => v.2.val 0) h
        change max p.val.2 0 = max q.val.2 0 at hc
        rwa [max_eq_left hp, max_eq_left hq] at hc
    · simp only [sphereCapSeamMap, hp, hq, ↓reduceIte] at he
      have h := B.sphereCapSeam_cross i (B.sphereCapSeam_core_source i p)
        (sphereCapSeam_ball_source q) he
      have hzero : halfSpaceOneLift (-q.val.2) = halfZero :=
        (congrArg Prod.snd h.1).symm.trans h.2
      exact (hq (neg_nonpos.mp (sphereCapHalfLift_nonpos hzero))).elim
  · by_cases hq : 0 ≤ q.val.2
    · simp only [sphereCapSeamMap, hp, hq, ↓reduceIte] at he
      have h := B.sphereCapSeam_cross i (B.sphereCapSeam_core_source i q)
        (sphereCapSeam_ball_source p) he.symm
      have hzero : halfSpaceOneLift (-p.val.2) = halfZero :=
        (congrArg Prod.snd h.1).symm.trans h.2
      exact (hp (neg_nonpos.mp (sphereCapHalfLift_nonpos hzero))).elim
    · simp only [sphereCapSeamMap, hp, hq, ↓reduceIte] at he
      have h := sphereCapBallCollar.injOn (sphereCapSeam_ball_source p)
        (sphereCapSeam_ball_source q) (B.sphereCapBall_injective i he)
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun v : ClosureSphere.{u} × EuclideanHalfSpace 1 => v.1) h
      · have hc := congrArg (fun v : ClosureSphere.{u} × EuclideanHalfSpace 1 => v.2.val 0) h
        change max (-p.val.2) 0 = max (-q.val.2) 0 at hc
        rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge hp)),
          max_eq_left (neg_nonneg.mpr (le_of_not_ge hq))] at hc
        linarith

def sphereCapSeamUnion (i : Fin B.sphereCount) : Set (SphereCapCut B) :=
  Sum.inl '' (B.sphere i).target ∪
    Sum.inr '' ({i} ×ˢ sphereCapBallCollar.{u}.target)

private theorem sphereCapSeamUnion_core (i : Fin B.sphereCount) (x : C.Carrier) :
    Sum.inl x ∈ B.sphereCapSeamUnion i ↔ x ∈ (B.sphere i).target := by
  simp [sphereCapSeamUnion]

private theorem sphereCapSeamUnion_ball (i j : Fin B.sphereCount) (x : ClosedCell 3) :
    Sum.inr (j, x) ∈ B.sphereCapSeamUnion i ↔ j = i ∧ x ∈ sphereCapBallCollar.{u}.target := by
  simp [sphereCapSeamUnion]

theorem sphereCapSeamUnion_isOpen (i : Fin B.sphereCount) : IsOpen (B.sphereCapSeamUnion i) :=
  (isOpenMap_inl _ (B.sphere i).open_target).union
    (isOpenMap_inr _ ((isOpen_discrete ({i} : Set (Fin B.sphereCount))).prod
      sphereCapBallCollar.{u}.open_target))

private theorem sphereCapSeamUnion_core_zero (i j : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.sphereCapLeft j z ∈ B.sphereCapSeamUnion i ↔ i = j := by
  rw [sphereCapLeft, B.sphereCapSeamUnion_core]
  have hz : (z, halfZero) ∈ (B.sphere j).source := by
    rw [B.sphere_source]
    change (0 : ℝ) < 1
    exact zero_lt_one
  constructor
  · intro hx
    by_contra hij
    exact (B.sphere_disjoint hij).le_bot ⟨hx, (B.sphere j).map_source' hz⟩
  · intro hij
    subst i
    exact (B.sphere j).map_source' hz

private theorem sphereCapSeamUnion_ball_zero (i j : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.sphereCapRight j z ∈ B.sphereCapSeamUnion i ↔ i = j := by
  rw [sphereCapRight, B.sphereCapSeamUnion_ball]
  have hz : (z, halfZero) ∈ sphereCapBallCollar.source := by
    rw [sphereCapBallCollar_source]
    change (0 : ℝ) < 1
    exact zero_lt_one
  constructor
  · intro hx
    exact hx.1.symm
  · intro hij
    exact ⟨hij.symm, sphereCapBallCollar_zero z ▸ sphereCapBallCollar.map_source' hz⟩

theorem sphereCapSeamUnion_saturated (i : Fin B.sphereCount)
    (x y : SphereCapCut B) (hxy : B.sphereCapGluing.rel x y) :
    x ∈ B.sphereCapSeamUnion i ↔ y ∈ B.sphereCapSeamUnion i := by
  rcases (B.sphereCapGluing_rel_iff x y).mp hxy with rfl | ⟨j, z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · rfl
  · rw [B.sphereCapSeamUnion_core_zero, B.sphereCapSeamUnion_ball_zero]
  · rw [B.sphereCapSeamUnion_ball_zero, B.sphereCapSeamUnion_core_zero]

def sphereCapSeamCoordinates (i : Fin B.sphereCount) (x : SphereCapCut B) :
    ClosureSphere.{u} × ℝ :=
  match x with
  | .inl x => (((B.sphere i).symm x).1, ((B.sphere i).symm x).2.val 0)
  | .inr x => ((sphereCapBallCollar.{u}.symm x.2).1, -(sphereCapBallCollar.{u}.symm x.2).2.val 0)

theorem sphereCapSeamCoordinates_continuousOn (i : Fin B.sphereCount) :
    ContinuousOn (B.sphereCapSeamCoordinates i) (B.sphereCapSeamUnion i) := by
  intro x hx
  cases x with
  | inl x =>
    have hx := (B.sphereCapSeamUnion_core i x).mp hx
    have hc := (B.sphere i).toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      ((B.sphere i).open_target.mem_nhds hx)
    have hf := hc.fst.prodMk
      (contMDiff_halfSpaceOneCoordinate.continuous.continuousAt.comp hc.snd)
    have h : ContinuousAt (B.sphereCapSeamCoordinates i) (Sum.inl x) :=
      (IsOpenEmbedding.inl.continuousAt_iff).mp hf
    exact h.continuousWithinAt
  | inr x =>
    have hx := (B.sphereCapSeamUnion_ball i x.1 x.2).mp hx
    have hc := sphereCapBallCollar.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      (sphereCapBallCollar.{u}.open_target.mem_nhds hx.2)
    have hg := hc.fst.prodMk
      (contMDiff_halfSpaceOneCoordinate.continuous.continuousAt.comp hc.snd).neg
    have hf := hg.comp continuous_snd.continuousAt
    have h : ContinuousAt (B.sphereCapSeamCoordinates i) (Sum.inr x) :=
      (IsOpenEmbedding.inr.continuousAt_iff).mp hf
    exact h.continuousWithinAt

theorem sphereCapSeamCoordinates_mem (i : Fin B.sphereCount) {x : SphereCapCut B}
    (hx : x ∈ B.sphereCapSeamUnion i) :
    B.sphereCapSeamCoordinates i x ∈ sphereSignedCollarSource := by
  cases x with
  | inl x =>
    have hx := (B.sphereCapSeamUnion_core i x).mp hx
    have hs := (B.sphere i).map_target' hx
    rw [B.sphere_source] at hs
    have hn := ((B.sphere i).symm x).2.property
    refine ⟨trivial, ?_, ?_⟩
    · change -1 < ((B.sphere i).symm x).2.val 0
      linarith
    · exact hs
  | inr x =>
    have hx := (B.sphereCapSeamUnion_ball i x.1 x.2).mp hx
    have hs := sphereCapBallCollar.map_target' hx.2
    rw [sphereCapBallCollar_source] at hs
    change (sphereCapBallCollar.{u}.symm x.2).2.val 0 < 1 at hs
    have hn := (sphereCapBallCollar.{u}.symm x.2).2.property
    refine ⟨trivial, ?_, ?_⟩
    · change -1 < -(sphereCapBallCollar.{u}.symm x.2).2.val 0
      linarith
    · change -(sphereCapBallCollar.{u}.symm x.2).2.val 0 < 1
      linarith

theorem sphereCapSeamCoordinates_fold (i : Fin B.sphereCount) {x : SphereCapCut B}
    (hx : x ∈ B.sphereCapSeamUnion i) :
    B.sphereCapSeamMap i
      ⟨B.sphereCapSeamCoordinates i x, B.sphereCapSeamCoordinates_mem i hx⟩ =
        B.sphereCapQuotientMap x := by
  cases x with
  | inl x =>
    have hx := (B.sphereCapSeamUnion_core i x).mp hx
    simp only [sphereCapSeamCoordinates, sphereCapSeamMap,
      ((B.sphere i).symm x).2.property, ↓reduceIte, halfSpaceOneLift_coord]
    exact congrArg B.sphereCapCore ((B.sphere i).right_inv' hx)
  | inr x =>
    have hx := (B.sphereCapSeamUnion_ball i x.1 x.2).mp hx
    have htag : x.1 = i := hx.1
    let v := sphereCapBallCollar.{u}.symm x.2
    by_cases hv0 : v.2.val 0 = 0
    · have hvz : v.2 = halfZero := by
        rw [← halfSpaceOneLift_coord v.2, hv0]
        exact sphereCapHalfLift_zero
      have hve : (v.1, halfZero) = v := Prod.ext rfl hvz.symm
      change (if 0 ≤ -v.2.val 0 then
        B.sphereCapCore (B.sphere i (v.1, halfSpaceOneLift (-v.2.val 0))) else
        B.sphereCapBall i (sphereCapBallCollar (v.1, halfSpaceOneLift (-(-v.2.val 0))))) = _
      rw [hv0, neg_zero, ite_eq_left le_rfl, sphereCapHalfLift_zero]
      change B.sphereCapCore (B.sphereMap i v.1) = _
      rw [B.sphereCap_attachment i v.1]
      have he : closureSphereToBall v.1 = x.2 :=
        (sphereCapBallCollar_zero v.1).symm.trans
          ((congrArg sphereCapBallCollar hve).trans (sphereCapBallCollar.right_inv' hx.2))
      rw [he]
      change B.sphereCapQuotientMap (Sum.inr (i, x.2)) = _
      exact congrArg B.sphereCapQuotientMap (congrArg (fun j => Sum.inr (j, x.2)) htag.symm)
    · have hn : ¬ 0 ≤ -v.2.val 0 := not_le.mpr (neg_neg_of_pos
        (lt_of_le_of_ne v.2.property (Ne.symm hv0)))
      dsimp only [v] at hn
      simp only [sphereCapSeamCoordinates, sphereCapSeamMap, hn, ↓reduceIte, neg_neg,
        halfSpaceOneLift_coord]
      have he := congrArg (B.sphereCapBall i) (sphereCapBallCollar.right_inv' hx.2)
      exact he.trans (congrArg B.sphereCapQuotientMap
        (congrArg (fun j => Sum.inr (j, x.2)) htag.symm))

theorem sphereCapSeamMap_range (i : Fin B.sphereCount) :
    range (B.sphereCapSeamMap i) = B.sphereCapQuotientMap '' B.sphereCapSeamUnion i := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : 0 ≤ p.val.2
    · simp only [sphereCapSeamMap, hp, ↓reduceIte]
      refine ⟨Sum.inl (B.sphere i (p.val.1, halfSpaceOneLift p.val.2)), ?_, rfl⟩
      exact (B.sphereCapSeamUnion_core i _).mpr
        ((B.sphere i).map_source' (B.sphereCapSeam_core_source i p))
    · simp only [sphereCapSeamMap, hp, ↓reduceIte]
      refine ⟨Sum.inr (i, sphereCapBallCollar (p.val.1, halfSpaceOneLift (-p.val.2))), ?_, rfl⟩
      exact (B.sphereCapSeamUnion_ball i i _).mpr
        ⟨rfl, sphereCapBallCollar.map_source' (sphereCapSeam_ball_source p)⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, B.sphereCapSeamCoordinates_fold i hx⟩

theorem sphereCapSeamMap_isOpen_range (i : Fin B.sphereCount) :
    IsOpen (range (B.sphereCapSeamMap i)) := by
  rw [B.sphereCapSeamMap_range]
  apply isOpen_quotient_mk_image_of_saturated
  · exact B.sphereCapSeamUnion_saturated i
  · exact B.sphereCapSeamUnion_isOpen i

theorem sphereCapSeamMap_preimage_range (i : Fin B.sphereCount) :
    B.sphereCapQuotientMap ⁻¹' range (B.sphereCapSeamMap i) = B.sphereCapSeamUnion i := by
  rw [B.sphereCapSeamMap_range]
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact (B.sphereCapSeamUnion_saturated i y x (Quotient.exact he)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

def sphereCapSeamHomeomorph (i : Fin B.sphereCount) :
    sphereCapSignedDomain.{u} ≃ₜ range (B.sphereCapSeamMap i) := by
  classical
  let e := Equiv.ofInjective (B.sphereCapSeamMap i) (B.sphereCapSeamMap_injective i)
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact (B.sphereCapSeamMap_continuous i).subtype_mk (fun p => mem_range_self p)
  · let V := range (B.sphereCapSeamMap i)
    have hquot : IsQuotientMap B.sphereCapQuotientMap := isQuotientMap_quotient_mk'
    have hquotV := hquot.restrictPreimage_isOpen (B.sphereCapSeamMap_isOpen_range i)
    have hxU : ∀ x : B.sphereCapQuotientMap ⁻¹' V,
        x.val ∈ B.sphereCapSeamUnion i := by
      intro x
      exact (B.sphereCapSeamMap_preimage_range i).subset x.property
    have hc : Continuous (fun x : B.sphereCapQuotientMap ⁻¹' V =>
        B.sphereCapSeamCoordinates i x.val) :=
      (B.sphereCapSeamCoordinates_continuousOn i).comp_continuous continuous_subtype_val hxU
    have heq : (fun x : B.sphereCapQuotientMap ⁻¹' V =>
        (e.symm (V.restrictPreimage B.sphereCapQuotientMap x)).val) =
        fun x => B.sphereCapSeamCoordinates i x.val := by
      funext x
      have he : e.symm (V.restrictPreimage B.sphereCapQuotientMap x) =
          ⟨B.sphereCapSeamCoordinates i x.val, B.sphereCapSeamCoordinates_mem i (hxU x)⟩ := by
        apply e.injective
        rw [e.apply_symm_apply]
        apply Subtype.ext
        exact (B.sphereCapSeamCoordinates_fold i (hxU x)).symm
      exact congrArg Subtype.val he
    apply hquotV.continuous_iff.mpr
    apply continuous_induced_rng.2
    change Continuous (fun x : B.sphereCapQuotientMap ⁻¹' V =>
      (e.symm (V.restrictPreimage B.sphereCapQuotientMap x)).val)
    rw [heq]
    exact hc

private theorem sphereCapSignedDomain_nonempty : Nonempty sphereCapSignedDomain.{u} := by
  classical
  exact ⟨⟨(Classical.choice inferInstance, 0), by constructor <;> norm_num⟩⟩

def sphereCapSignedSeam (i : Fin B.sphereCount) :
    OpenPartialHomeomorph (ClosureSphere.{u} × ℝ) B.SphereCapQuotient :=
  let V : Opens B.SphereCapQuotient :=
    ⟨range (B.sphereCapSeamMap i), B.sphereCapSeamMap_isOpen_range i⟩
  let e := B.sphereCapSeamHomeomorph i
  let hV : Nonempty V := Nonempty.map e sphereCapSignedDomain_nonempty
  ((sphereCapSignedDomain.openPartialHomeomorphSubtypeCoe
    sphereCapSignedDomain_nonempty).symm.trans e.toOpenPartialHomeomorph).trans
      (V.openPartialHomeomorphSubtypeCoe hV)

theorem sphereCapSignedSeam_source (i : Fin B.sphereCount) :
    (B.sphereCapSignedSeam i).source = sphereSignedCollarSource := by
  simp only [sphereCapSignedSeam, OpenPartialHomeomorph.trans_source,
    Opens.openPartialHomeomorphSubtypeCoe_source, Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ, inter_univ, OpenPartialHomeomorph.symm_source,
    Opens.openPartialHomeomorphSubtypeCoe_target]
  rfl

theorem sphereCapSignedSeam_apply (i : Fin B.sphereCount) (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ sphereSignedCollarSource) :
    B.sphereCapSignedSeam i p = B.sphereCapSeamMap i ⟨p, hp⟩ := by
  let a := sphereCapSignedDomain.openPartialHomeomorphSubtypeCoe sphereCapSignedDomain_nonempty
  have hpa : p ∈ a.target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hp
  have ha : a.symm p = ⟨p, hp⟩ := Subtype.ext (a.right_inv hpa)
  change (B.sphereCapSeamHomeomorph i (a.symm p)).val = B.sphereCapSeamMap i ⟨p, hp⟩
  rw [ha]
  rfl

theorem sphereCapSignedSeam_target (i : Fin B.sphereCount) :
    (B.sphereCapSignedSeam i).target = range (B.sphereCapSeamMap i) := by
  simp only [sphereCapSignedSeam, OpenPartialHomeomorph.trans_target,
    Opens.openPartialHomeomorphSubtypeCoe_target, Homeomorph.toOpenPartialHomeomorph_target,
    OpenPartialHomeomorph.symm_target, Opens.openPartialHomeomorphSubtypeCoe_source,
    preimage_univ, inter_univ]
  rfl

theorem sphereCapSignedSeam_disjoint :
    Pairwise fun i j => Disjoint (B.sphereCapSignedSeam i).target
      (B.sphereCapSignedSeam j).target := by
  intro i j hij
  rw [B.sphereCapSignedSeam_target i, B.sphereCapSignedSeam_target j,
    B.sphereCapSeamMap_range i, B.sphereCapSeamMap_range j, disjoint_left]
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxj := (B.sphereCapSeamUnion_saturated j y x (Quotient.exact hyx)).mp hy
  cases x with
  | inl x =>
    have hi := (B.sphereCapSeamUnion_core i x).mp hx
    have hj := (B.sphereCapSeamUnion_core j x).mp hxj
    exact (B.sphere_disjoint hij).le_bot ⟨hi, hj⟩
  | inr x =>
    have hi := (B.sphereCapSeamUnion_ball i x.1 x.2).mp hx
    have hj := (B.sphereCapSeamUnion_ball j x.1 x.2).mp hxj
    exact hij (hi.1.symm.trans hj.1)

theorem sphereCapSignedSeam_zero (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.sphereCapSignedSeam i (z, 0) = B.sphereCapCore (B.sphereMap i z) := by
  rw [B.sphereCapSignedSeam_apply i (z, 0) (by constructor <;> norm_num)]
  exact B.sphereCapSeamMap_zero i z

theorem sphereCapSignedSeam_positive (i : Fin B.sphereCount) (z : ClosureSphere.{u})
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    B.sphereCapSignedSeam i (z, s) =
      B.sphereCapCore (B.sphere i (z, halfPoint s hs)) := by
  rw [B.sphereCapSignedSeam_apply i (z, s) ⟨trivial, by linarith, hs1⟩]
  simp only [sphereCapSeamMap, hs, ↓reduceIte, sphereCapHalfLift_halfPoint s hs]

theorem sphereCapSignedSeam_negative (i : Fin B.sphereCount) (z : ClosureSphere.{u})
    (s : ℝ) (hs : s ≤ 0) (hs1 : -1 < s) :
    B.sphereCapSignedSeam i (z, s) = B.sphereCapBall i
      (sphereCapBallCollar (z, halfPoint (-s) (neg_nonneg.mpr hs))) := by
  by_cases hn : 0 ≤ s
  · have he : s = 0 := le_antisymm hs hn
    subst s
    rw [B.sphereCapSignedSeam_zero i z, B.sphereCap_attachment i z]
    congr 1
    simpa only [neg_zero, halfZero] using (sphereCapBallCollar_zero z).symm
  · rw [B.sphereCapSignedSeam_apply i (z, s) ⟨trivial, hs1, hs.trans_lt zero_lt_one⟩]
    simp only [sphereCapSeamMap, hn, ↓reduceIte,
      sphereCapHalfLift_halfPoint (-s) (neg_nonneg.mpr hs)]

end GC.GraphManifold.MixedBoundaryCertificate
