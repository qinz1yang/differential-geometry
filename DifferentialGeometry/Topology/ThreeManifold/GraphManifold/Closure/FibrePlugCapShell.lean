import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapRadial
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCarrier

/-!
The actual bounded cap shell lifted through the native zero-sphere cut.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable {W : CompactCarrier.{u}}

def boundedPlugCutCollars
    (d : PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞) : SphereCutSignedCollars W :=
  Function.const (Fin 1) d

theorem boundedPlugCutCollars_source
    (d : PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource) :
    ∀ j, (boundedPlugCutCollars d j).source = sphereSignedCollarSource :=
  Function.const (Fin 1) hs

theorem boundedPlugCutCollars_disjoint
    (d : PartialDiffeomorph sphereSignedCollarModel W.model
      (ClosureSphere.{u} × ℝ) W.Carrier ∞) :
    Pairwise fun i j => Disjoint (boundedPlugCutCollars d i).target
      (boundedPlugCutCollars d j).target := by
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

variable (d : PartialDiffeomorph sphereSignedCollarModel W.model
  (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior) {n : ℕ} (A : BoundaryTori W n)
  (hA : W.model.boundary W.Carrier = A.image)
  (hav : ∀ i, Disjoint (A.collar i).target d.target)

abbrev boundedPlugCutCarrier : CompactCarrier.{u} :=
  sphereCutCarrier (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
    (boundedPlugCutCollars_disjoint d)

abbrev boundedPlugCutBoundary : MixedBoundaryCertificate (boundedPlugCutCarrier d hs) :=
  sphereCutMixedBoundary (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
    (boundedPlugCutCollars_disjoint d) (Function.const (Fin 1) hI) A hA
      (fun i => Function.const (Fin 1) (hav i))

def boundedPlugCapShellSign (i : Fin 2) : ℝ :=
  if sphereCutBoundarySide i then -1 else 1

theorem boundedPlugCapShellSign_ne_zero (i : Fin 2) : boundedPlugCapShellSign i ≠ 0 := by
  fin_cases i <;> norm_num [boundedPlugCapShellSign, sphereCutBoundarySide]

theorem boundedPlugCapShellSign_abs (i : Fin 2) : |boundedPlugCapShellSign i| = 1 := by
  fin_cases i <;> norm_num [boundedPlugCapShellSign, sphereCutBoundarySide]

variable (E : ElementaryPresentation W) {j : Fin E.toTorus.pairing.count} {b : Bool}
  (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))

def boundedPlugCapShellPoint (i : Fin 2) (p : ClosureSphere.{u} × ℝ) : W.Carrier :=
  E.boundedSplitTubeMap h hlin (p.1.down, boundedPlugCapShellSign i * boundedPlugCapProfile p.2)

theorem boundedPlugCapShell_profile_bounds {r : ℝ} (hr : 1 < r) (hr1 : r < 5 / 2) :
    0 < boundedPlugCapProfile r ∧ boundedPlugCapProfile r < 5 / 2 := by
  have h0 : boundedPlugCapProfile 1 = 0 := by
    rw [boundedPlugCapProfile_inner (by norm_num)]
    norm_num
  have h1 : boundedPlugCapProfile (5 / 2) = 5 / 2 :=
    boundedPlugCapProfile_outer (by norm_num)
  constructor
  · simpa only [h0] using boundedPlugCapProfile_strictMono hr
  · simpa only [h1] using boundedPlugCapProfile_strictMono hr1

include heq in
theorem boundedPlugCapShellPoint_offZero (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hr : 1 < p.2) (hr1 : p.2 < 5 / 2) :
    boundedPlugCapShellPoint E h hlin i p ∉ sphereCutAmbientZero (boundedPlugCutCollars d) := by
  intro hzero
  obtain ⟨k, z, hz⟩ := mem_iUnion.mp hzero
  have hz0 : d (z, 0) = boundedPlugCapShellPoint E h hlin i p := hz
  rw [heq] at hz0
  have hb := boundedPlugCapShell_profile_bounds hr hr1
  have ha : |boundedPlugCapShellSign i * boundedPlugCapProfile p.2| < 3 := by
    rw [abs_mul, boundedPlugCapShellSign_abs, abs_of_pos hb.1, one_mul]
    linarith
  have hh := E.boundedSplitTubeMap_injOn h hlin (by norm_num) ha hz0
  have hlevel := congrArg Prod.snd hh
  exact (mul_ne_zero (boundedPlugCapShellSign_ne_zero i) hb.1.ne') hlevel.symm

def boundedPlugCapShellLift (i : Fin 2) (p : ClosureSphere.{u} × ℝ) :
    (boundedPlugCutCarrier d hs).Carrier :=
  sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
      (boundedPlugCapShellPoint E h hlin i p)

include heq in
theorem boundedPlugCapShellLift_fold (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hr : 1 < p.2) (hr1 : p.2 < 5 / 2) :
    sphereCutFold (boundedPlugCutCollars d) (boundedPlugCapShellLift d hs E h hlin i p) =
      boundedPlugCapShellPoint E h hlin i p :=
  sphereCutAmbientPartialDiffeomorph_fold _ _ _ _
    (boundedPlugCapShellPoint_offZero d E h hlin heq i p hr hr1)

include heq in
theorem boundedPlugCapShellLift_coreOpen (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hr : 1 < p.2) (hr1 : p.2 < 5 / 2) :
    boundedPlugCapShellLift d hs E h hlin i p ∈
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCoreOpen := by
  intro hx
  obtain ⟨k, z, hz⟩ := mem_iUnion.mp hx
  have hf := congrArg (sphereCutFold (boundedPlugCutCollars d)) hz
  have hp : (z, halfZero) ∈ sphereHalfCollarSource := by change (0 : ℝ) < 1; norm_num
  change sphereCutFold (boundedPlugCutCollars d)
    (sphereCutFullCollar (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
      (boundedPlugCutCollars_disjoint d) 0 (sphereCutBoundarySide k) (z, halfZero)) = _ at hf
  rw [sphereCutFullCollar_fold _ _ _ _ _ _ hp] at hf
  rw [boundedPlugCapShellLift_fold d hs E h hlin heq i p hr hr1] at hf
  have hh : d (z, 0) = boundedPlugCapShellPoint E h hlin i p := by
    change d (z, if sphereCutBoundarySide k then -(0 : ℝ) else 0) = _ at hf
    simpa only [neg_zero, ite_self] using hf
  apply boundedPlugCapShellPoint_offZero d E h hlin heq i p hr hr1
  exact mem_iUnion.mpr ⟨0, z, hh⟩

def boundedPlugCapShell (i : Fin 2) (p : ClosureSphere.{u} × ℝ) :
    (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.Carrier :=
  (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCore
    (boundedPlugCapShellLift d hs E h hlin i p)

def boundedPlugCapShellSignDiffeomorph (i : Fin 2) : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ :=
  if sphereCutBoundarySide i then (ContinuousLinearEquiv.neg ℝ).toDiffeomorph
    else Diffeomorph.refl 𝓘(ℝ) ℝ ∞

theorem boundedPlugCapShellSignDiffeomorph_apply (i : Fin 2) (r : ℝ) :
    boundedPlugCapShellSignDiffeomorph i r = boundedPlugCapShellSign i * r := by
  fin_cases i <;> simp [boundedPlugCapShellSignDiffeomorph, sphereCutBoundarySide,
    boundedPlugCapShellSign]

def boundedPlugCapShellCoordinates (i : Fin 2) :
    (ClosureSphere.{u} × ℝ) ≃ₘ⟮sphereSignedCollarModel, (𝓡 2).prod 𝓘(ℝ)⟯
      (SphereTwo × ℝ) :=
  (uliftDiffeomorph (I := 𝓡 2) (M := SphereTwo)).symm.prodCongr
    (boundedPlugCapProfileDiffeomorph.trans (boundedPlugCapShellSignDiffeomorph i))

theorem boundedPlugCapShellCoordinates_apply (i : Fin 2) (p : ClosureSphere.{u} × ℝ) :
    boundedPlugCapShellCoordinates i p =
      (p.1.down, boundedPlugCapShellSign i * boundedPlugCapProfile p.2) := by
  apply Prod.ext
  · rfl
  · exact boundedPlugCapShellSignDiffeomorph_apply i (boundedPlugCapProfile p.2)

theorem boundedPlugCapShellPoint_local (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hr : 1 < p.2) (hr1 : p.2 < 5 / 2) :
    IsLocalDiffeomorphAt sphereSignedCollarModel W.model ∞
      (boundedPlugCapShellPoint E h hlin i) p := by
  have hb := boundedPlugCapShell_profile_bounds hr hr1
  have hraw : |(boundedPlugCapShellCoordinates i p).2| < 3 := by
    rw [boundedPlugCapShellCoordinates_apply, abs_mul, boundedPlugCapShellSign_abs,
      abs_of_pos hb.1, one_mul]
    linarith
  have hh := ((boundedPlugCapShellCoordinates i).isLocalDiffeomorph p).comp W.model W.Carrier
    (E.boundedSplitTubeMap_local h hlin hraw)
  have he : E.boundedSplitTubeMap h hlin ∘ boundedPlugCapShellCoordinates i =
      boundedPlugCapShellPoint E h hlin i := by
    funext q
    rw [Function.comp_apply, boundedPlugCapShellCoordinates_apply]
    rfl
  rwa [he] at hh

include heq in
theorem boundedPlugCapShellLift_local (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hr : 1 < p.2) (hr1 : p.2 < 5 / 2) :
    IsLocalDiffeomorphAt sphereSignedCollarModel (boundedPlugCutCarrier d hs).model ∞
      (boundedPlugCapShellLift d hs E h hlin i) p := by
  have hx := boundedPlugCapShellPoint_offZero d E h hlin heq i p hr hr1
  have hsource : boundedPlugCapShellPoint E h hlin i p ∈
      (sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
        (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)).source := by
    rw [sphereCutAmbientPartialDiffeomorph_source]
    exact hx
  exact (boundedPlugCapShellPoint_local E h hlin i p hr hr1).comp _ _
    ((sphereCutAmbientPartialDiffeomorph (boundedPlugCutCollars d)
      (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)).isLocalDiffeomorphAt
        W.model (boundedPlugCutCarrier d hs).model ∞ hsource)

include heq in
theorem boundedPlugCapShell_local (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hr : 1 < p.2) (hr1 : p.2 < 5 / 2) :
    IsLocalDiffeomorphAt sphereSignedCollarModel
      (boundedPlugCutBoundary d hs hI A hA hav).sphereCapCarrier.model ∞
      (boundedPlugCapShell d hs hI A hA hav E h hlin i) p := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  let := B.sphereCapQuotientChartedSpace
  let hx := boundedPlugCapShellLift_coreOpen d hs hI A hA hav E h hlin heq i p hr hr1
  let y : B.sphereCapCoreOpen := ⟨boundedPlugCapShellLift d hs E h hlin i p, hx⟩
  let q := B.sphereCapCoreOpenDiffeomorph B.exists_sphereCapQuotientAtlas.choose_spec.2 y
  have hys : boundedPlugCapShellLift d hs E h hlin i p ∈ q.source := by
    rw [B.sphereCapCoreOpenDiffeomorph_source]
    exact hx
  have hl := boundedPlugCapShellLift_local d hs E h hlin heq i p hr hr1
  have hq := q.isLocalDiffeomorphAt (boundedPlugCutCarrier d hs).model (𝓡∂ 3) ∞ hys
  have hc := hl.comp (𝓡∂ 3) B.SphereCapQuotient hq
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (hg := hc)
  filter_upwards [hl.contMDiffAt.continuousAt.preimage_mem_nhds
    (B.sphereCapCoreOpen.isOpen.mem_nhds hx)] with x hx
  exact (B.sphereCapCoreOpenDiffeomorph_apply
    B.exists_sphereCapQuotientAtlas.choose_spec.2 y hx).symm

include heq in
theorem boundedPlugCapShell_eq_normal (i : Fin 2) (z : ClosureSphere.{u})
    {r : ℝ} (hr : 1 < r) (hr1 : r ≤ 5 / 4) :
    boundedPlugCapShell d hs hI A hA hav E h hlin i (z, r) =
      (boundedPlugCutBoundary d hs hI A hA hav).boundedPlugCapNormal i (z, r) := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  have hb := boundedPlugCapShell_profile_bounds hr (by linarith)
  have hs0 : 0 ≤ 2 * r - 2 := by linarith
  have hp : (z, halfPoint (2 * r - 2) hs0) ∈ sphereHalfCollarSource := by
    change 2 * r - 2 < 1
    linarith
  have hf : sphereCutFold (boundedPlugCutCollars d)
      (B.sphere i (z, halfPoint (2 * r - 2) hs0)) =
      boundedPlugCapShellPoint E h hlin i (z, r) := by
    change sphereCutFold (boundedPlugCutCollars d)
      (sphereCutFullCollar (boundedPlugCutCollars d) (boundedPlugCutCollars_source d hs)
        (boundedPlugCutCollars_disjoint d) 0 (sphereCutBoundarySide i) _) = _
    rw [sphereCutFullCollar_fold _ _ _ _ _ _ hp]
    change d (z, if sphereCutBoundarySide i then -(2 * r - 2) else 2 * r - 2) = _
    rw [heq]
    unfold boundedPlugCapShellPoint
    rw [boundedPlugCapProfile_inner hr1]
    fin_cases i <;> simp [boundedPlugCapShellSign, sphereCutBoundarySide]
  have hzero := boundedPlugCapShellPoint_offZero d E h hlin heq i (z, r) hr (by linarith)
  have hxo : B.sphere i (z, halfPoint (2 * r - 2) hs0) ∈
      sphereCutOffZero (boundedPlugCutCollars d) := by
    change sphereCutFold _ _ ∉ sphereCutAmbientZero _
    rw [hf]
    exact hzero
  have hyo : boundedPlugCapShellLift d hs E h hlin i (z, r) ∈
      sphereCutOffZero (boundedPlugCutCollars d) := by
    change sphereCutFold _ _ ∉ sphereCutAmbientZero _
    rw [boundedPlugCapShellLift_fold d hs E h hlin heq i (z, r) hr (by linarith)]
    exact hzero
  have he : B.sphere i (z, halfPoint (2 * r - 2) hs0) =
      boundedPlugCapShellLift d hs E h hlin i (z, r) :=
    sphereCutFold_injOn_offZero _ (boundedPlugCutCollars_source d hs)
      (boundedPlugCutCollars_disjoint d) hxo hyo
      (hf.trans (boundedPlugCapShellLift_fold d hs E h hlin heq i (z, r) hr
        (by linarith)).symm)
  rw [B.boundedPlugCapNormal_positive i z hr.le hr1]
  exact congrArg B.sphereCapCore he.symm

include heq in
theorem boundedPlugCapShell_injOn (i : Fin 2) :
    InjOn (boundedPlugCapShell d hs hI A hA hav E h hlin i)
      (univ ×ˢ Ioo (1 : ℝ) (5 / 2)) := by
  intro p hp q hq hpq
  let B := boundedPlugCutBoundary d hs hI A hA hav
  have hh : boundedPlugCapShellLift d hs E h hlin i p =
      boundedPlugCapShellLift d hs E h hlin i q := B.sphereCapCore_injective hpq
  have hf := congrArg (sphereCutFold (boundedPlugCutCollars d)) hh
  rw [boundedPlugCapShellLift_fold d hs E h hlin heq i p hp.2.1 hp.2.2,
    boundedPlugCapShellLift_fold d hs E h hlin heq i q hq.2.1 hq.2.2] at hf
  have hb := boundedPlugCapShell_profile_bounds hp.2.1 hp.2.2
  have hc := boundedPlugCapShell_profile_bounds hq.2.1 hq.2.2
  have ha : |boundedPlugCapShellSign i * boundedPlugCapProfile p.2| < 3 := by
    rw [abs_mul, boundedPlugCapShellSign_abs, abs_of_pos hb.1, one_mul]
    linarith
  have hd : |boundedPlugCapShellSign i * boundedPlugCapProfile q.2| < 3 := by
    rw [abs_mul, boundedPlugCapShellSign_abs, abs_of_pos hc.1, one_mul]
    linarith
  have he := E.boundedSplitTubeMap_injOn h hlin ha hd hf
  apply Prod.ext
  · exact ULift.ext (congrArg Prod.fst he)
  · apply boundedPlugCapProfile_strictMono.injective
    exact mul_left_cancel₀ (boundedPlugCapShellSign_ne_zero i) (congrArg Prod.snd he)

include heq in
theorem boundedPlugCapShell_disjoint_ball (i k : Fin 2) :
    Disjoint (boundedPlugCapShell d hs hI A hA hav E h hlin i ''
      (univ ×ˢ Ioo (1 : ℝ) (5 / 2)))
      (range ((boundedPlugCutBoundary d hs hI A hA hav).sphereCapBall k)) := by
  let B := boundedPlugCutBoundary d hs hI A hA hav
  rw [disjoint_left]
  rintro y ⟨p, hp, rfl⟩ hball
  have hmem : boundedPlugCapShell d hs hI A hA hav E h hlin i p ∈
      range B.sphereCapCore ∩ range (B.sphereCapBall k) :=
    ⟨⟨boundedPlugCapShellLift d hs E h hlin i p, rfl⟩, hball⟩
  obtain ⟨z, hz⟩ := (B.sphereCapCore_ball_intersection k).subset hmem
  have he : B.sphereMap k z = boundedPlugCapShellLift d hs E h hlin i p :=
    B.sphereCapCore_injective hz
  have hx := boundedPlugCapShellLift_coreOpen d hs hI A hA hav E h hlin heq
    i p hp.2.1 hp.2.2
  exact hx (mem_iUnion.mpr ⟨k, z, he⟩)

end GC.GraphManifold
