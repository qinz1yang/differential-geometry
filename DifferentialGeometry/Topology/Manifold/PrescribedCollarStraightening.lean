import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.CollarStraighteningProducer
import DifferentialGeometry.Topology.Diffeomorph.Flow

set_option autoImplicit false

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Collar

private def halfLineBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

private theorem halfLineBump_eq_zero_of_dist {x : ℝ} (hx : 1 / 4 ≤ |x - 1 / 2|) :
    halfLineBump x = 0 := by
  apply halfLineBump.zero_of_le_dist
  rw [Real.dist_eq]
  exact hx

private theorem halfLineBump_eq_one_of_dist {x : ℝ} (hx : |x - 1 / 2| ≤ 1 / 8) :
    halfLineBump x = 1 := by
  apply halfLineBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  exact hx

private def prescribedField (ε : ℝ) : ℝ → ℝ := fun x => halfLineBump (x / ε)

private theorem prescribedField_contDiff (ε : ℝ) : ContDiff ℝ ∞ (prescribedField ε) :=
  halfLineBump.contDiff.comp (contDiff_id.div_const ε)

private theorem prescribedField_eq_zero_of_le {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 4) :
    prescribedField ε x = 0 := by
  apply halfLineBump_eq_zero_of_dist
  have h1 : x / ε ≤ 1 / 4 := by
    rw [div_le_iff₀ hε]
    linarith
  have h : |x / ε - 1 / 2| = 1 / 2 - x / ε := by
    rw [abs_of_nonpos (by linarith : x / ε - 1 / 2 ≤ 0)]
    ring
  rw [h]
  linarith

private theorem prescribedField_eq_zero_of_ge {ε x : ℝ} (hε : 0 < ε) (hx : 3 * ε / 4 ≤ x) :
    prescribedField ε x = 0 := by
  apply halfLineBump_eq_zero_of_dist
  have h1 : (3 : ℝ) / 4 ≤ x / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have h : |x / ε - 1 / 2| = x / ε - 1 / 2 := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x / ε - 1 / 2)]
  rw [h]
  linarith

private theorem prescribedField_eq_one {ε x : ℝ} (hε : 0 < ε) (hx : |x - ε / 2| ≤ ε / 8) :
    prescribedField ε x = 1 := by
  apply halfLineBump_eq_one_of_dist
  have hsub : x / ε - 1 / 2 = (x - ε / 2) / ε := by
    field_simp
  have h : |x / ε - 1 / 2| = |x - ε / 2| / ε := by
    rw [hsub, abs_div, abs_of_pos hε]
  rw [h, div_le_iff₀ hε]
  linarith

private theorem prescribedField_tsupport_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (prescribedField ε) ⊆ Set.Icc (ε / 4) (3 * ε / 4) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hxI
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
  rcases hxI with hxI | hxI
  · exact hx (prescribedField_eq_zero_of_le hε hxI.le)
  · exact hx (prescribedField_eq_zero_of_ge hε (by linarith : 3 * ε / 4 ≤ x))

private theorem prescribedField_hasCompactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (prescribedField ε) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (prescribedField_tsupport_subset hε)

private theorem prescribedField_contMDiff (ε : ℝ) :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      (fun x : ℝ => (⟨x, prescribedField ε x⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr (prescribedField_contDiff ε)

private noncomputable def prescribedFlow (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞ :=
  Diffeomorph.compactSupportFlow (prescribedField ε) (prescribedField_contMDiff ε)
    (prescribedField_hasCompactSupport hε) t

private theorem prescribedFlow_eqOn_compl (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    Set.EqOn (prescribedFlow ε hε t) id (tsupport (prescribedField ε))ᶜ ∧
      Set.EqOn (prescribedFlow ε hε t).symm id (tsupport (prescribedField ε))ᶜ :=
  Diffeomorph.compactSupportFlow_eqOn_compl_tsupport (prescribedField ε)
    (prescribedField_contMDiff ε) (prescribedField_hasCompactSupport hε) t

private theorem prescribedFlow_eq_self_of_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) {x : ℝ}
    (hx : x ≤ ε / 4) : prescribedFlow ε hε t x = x :=
  Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero (prescribedField ε)
    (prescribedField_contMDiff ε) (prescribedField_hasCompactSupport hε)
    (prescribedField_eq_zero_of_le hε hx) t

private theorem prescribedFlow_eq_self_of_ge {ε : ℝ} (hε : 0 < ε) (t : ℝ) {x : ℝ}
    (hx : 3 * ε / 4 ≤ x) : prescribedFlow ε hε t x = x :=
  Diffeomorph.compactSupportFlow_apply_eq_self_of_eq_zero (prescribedField ε)
    (prescribedField_contMDiff ε) (prescribedField_hasCompactSupport hε)
    (prescribedField_eq_zero_of_ge hε hx) t

private theorem prescribedFlow_symm_eq_self_of_ge {ε : ℝ} (hε : 0 < ε) (t : ℝ) {x : ℝ}
    (hx : 3 * ε / 4 ≤ x) : (prescribedFlow ε hε t).symm x = x :=
  Diffeomorph.compactSupportFlow_symm_apply_eq_self_of_eq_zero (prescribedField ε)
    (prescribedField_contMDiff ε) (prescribedField_hasCompactSupport hε)
    (prescribedField_eq_zero_of_ge hε hx) t

private theorem prescribedFlow_gt {ε : ℝ} (hε : 0 < ε) (t x : ℝ) (hx : ε / 4 < x) :
    ε / 4 < prescribedFlow ε hε t x := by
  by_contra h
  push Not at h
  have hfix : prescribedFlow ε hε t (prescribedFlow ε hε t x) = prescribedFlow ε hε t x :=
    prescribedFlow_eq_self_of_le hε t h
  have hxx : prescribedFlow ε hε t x = x := (prescribedFlow ε hε t).injective hfix
  linarith

private theorem prescribedFlow_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ prescribedFlow ε hε t x := by
  rcases le_or_gt x (ε / 4) with h | h
  · rw [prescribedFlow_eq_self_of_le hε t h]
    exact hx
  · exact (lt_trans (by linarith : (0 : ℝ) < ε / 4) (prescribedFlow_gt hε t x h)).le

private theorem prescribedFlow_symm {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (prescribedFlow ε hε t).symm = prescribedFlow ε hε (-t) :=
  Diffeomorph.compactSupportFlow_symm (prescribedField ε) (prescribedField_contMDiff ε)
    (prescribedField_hasCompactSupport hε) t

private theorem exists_prescribedFlow_ne_refl (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, prescribedFlow ε hε t ≠ Diffeomorph.refl 𝓘(ℝ) ℝ ∞ := by
  have hB : IsCompact (Metric.closedBall (ε / 2) (ε / 32)) := isCompact_closedBall _ _
  have hBU : Metric.closedBall (ε / 2) (ε / 32) ⊆ Metric.ball (ε / 2) (ε / 16) := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  have hrate : ∀ x ∈ Metric.ball (ε / 2) (ε / 16),
      NormedSpace.fromTangentSpace x
        (mfderiv 𝓘(ℝ) 𝓘(ℝ) (id : ℝ → ℝ) x (prescribedField ε x)) = 1 := by
    intro x hx
    have hx1 : prescribedField ε x = 1 := by
      apply prescribedField_eq_one hε
      rw [Metric.mem_ball, Real.dist_eq] at hx
      rw [abs_lt] at hx
      rw [abs_le]
      constructor <;> linarith
    rw [hx1]
    simp only [mfderiv_id]
    rfl
  obtain ⟨δ, hδ, hflow⟩ :=
    Diffeomorph.exists_pos_compactSupportFlow_height (prescribedField ε)
    (prescribedField_contMDiff ε) (prescribedField_hasCompactSupport hε) (id : ℝ → ℝ)
    hB Metric.isOpen_ball hBU hrate
  refine ⟨δ / 2, ?_⟩
  intro hrefl
  have hx0 : ε / 2 ∈ Metric.closedBall (ε / 2) (ε / 32) := by
    rw [Metric.mem_closedBall]
    simp only [dist_self]
    linarith
  have ht : δ / 2 ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
  have hval : prescribedFlow ε hε (δ / 2) (ε / 2) = ε / 2 + δ / 2 := by
    have := (hflow (ε / 2) hx0 (δ / 2) ht).2
    simp only [id_eq] at this
    simpa only [prescribedFlow] using this
  have hself : prescribedFlow ε hε (δ / 2) (ε / 2) = ε / 2 := by
    rw [hrefl]
    rfl
  linarith

private theorem halfSpaceOneLift_coordinate (t : ℝ) : (halfSpaceOneLift t).1 0 = max t 0 := rfl

private theorem halfSpaceOneLift_eq_self_apply (t : EuclideanHalfSpace 1) :
    halfSpaceOneLift (t.1 0) = t := by
  rw [halfSpaceOneLift_eq]
  have heq : (⟨max 0 (t.1 0), le_max_left 0 (t.1 0)⟩ : Set.Ici (0 : ℝ)) =
      halfSpaceOneHomeomorph t := Subtype.ext (max_eq_right t.2)
  rw [heq]
  exact halfSpaceOneHomeomorph.symm_apply_apply t

private theorem transportContMDiff (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞
      (fun t : EuclideanHalfSpace 1 => halfSpaceOneLift (prescribedFlow ε hε s (t.1 0))) := by
  have h1 : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : EuclideanHalfSpace 1 => prescribedFlow ε hε s (t.1 0)) :=
    (prescribedFlow ε hε s).contMDiff_toFun.comp contMDiff_halfSpaceOneCoordinate
  have hrange : ∀ t : EuclideanHalfSpace 1,
      prescribedFlow ε hε s (t.1 0) ∈ Set.Ici (0 : ℝ) := fun t =>
    prescribedFlow_nonneg hε s t.2
  exact contMDiffOn_univ.mp
    ((contMDiffOn_halfSpaceOneLift).comp_contMDiff h1 hrange).contMDiffOn

private noncomputable def halfLineTransport (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) ∞ where
  toEquiv :=
    { toFun := fun t => halfSpaceOneLift (prescribedFlow ε hε s (t.1 0))
      invFun := fun t => halfSpaceOneLift (prescribedFlow ε hε (-s) (t.1 0))
      left_inv := by
        intro t
        have hsymm : prescribedFlow ε hε (-s) (prescribedFlow ε hε s (t.1 0)) = t.1 0 := by
          rw [← prescribedFlow_symm hε s]
          exact Diffeomorph.symm_apply_apply _ _
        have hcoord : (halfSpaceOneLift (prescribedFlow ε hε s (t.1 0))).1 0
            = prescribedFlow ε hε s (t.1 0) := by
          rw [halfSpaceOneLift_coordinate, max_eq_left (prescribedFlow_nonneg hε s t.2)]
        change halfSpaceOneLift (prescribedFlow ε hε (-s)
          ((halfSpaceOneLift (prescribedFlow ε hε s (t.1 0))).1 0)) = t
        rw [hcoord, hsymm]
        exact halfSpaceOneLift_eq_self_apply t
      right_inv := by
        intro t
        have hsymm : prescribedFlow ε hε s (prescribedFlow ε hε (-s) (t.1 0)) = t.1 0 := by
          rw [← prescribedFlow_symm hε s]
          exact Diffeomorph.apply_symm_apply _ _
        have hcoord : (halfSpaceOneLift (prescribedFlow ε hε (-s) (t.1 0))).1 0
            = prescribedFlow ε hε (-s) (t.1 0) := by
          rw [halfSpaceOneLift_coordinate, max_eq_left (prescribedFlow_nonneg hε (-s) t.2)]
        change halfSpaceOneLift (prescribedFlow ε hε s
          ((halfSpaceOneLift (prescribedFlow ε hε (-s) (t.1 0))).1 0)) = t
        rw [hcoord, hsymm]
        exact halfSpaceOneLift_eq_self_apply t }
  contMDiff_toFun := transportContMDiff ε hε s
  contMDiff_invFun := transportContMDiff ε hε (-s)

private theorem halfLineTransport_apply (ε : ℝ) (hε : 0 < ε) (s : ℝ)
    (t : EuclideanHalfSpace 1) :
    halfLineTransport ε hε s t = halfSpaceOneLift (prescribedFlow ε hε s (t.1 0)) := rfl

private theorem halfLineTransport_symm_apply (ε : ℝ) (hε : 0 < ε) (s : ℝ)
    (t : EuclideanHalfSpace 1) :
    (halfLineTransport ε hε s).symm t = halfSpaceOneLift (prescribedFlow ε hε (-s) (t.1 0)) :=
  rfl

private theorem refl_apply_halfSpace (t : EuclideanHalfSpace 1) :
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞) t = t := rfl

private theorem halfLineTransport_ne_refl {ε : ℝ} (hε : 0 < ε) {s : ℝ}
    (hs : prescribedFlow ε hε s ≠ Diffeomorph.refl 𝓘(ℝ) ℝ ∞) :
    halfLineTransport ε hε s ≠ Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞ := by
  intro hrefl
  apply hs
  refine Diffeomorph.ext fun x => ?_
  rcases le_or_gt x 0 with hx | hx
  · have hmem : x ∉ tsupport (prescribedField ε) := by
      intro hmem
      have hb := prescribedField_tsupport_subset hε hmem
      rw [Set.mem_Icc] at hb
      linarith [hb.1]
    exact (prescribedFlow_eqOn_compl ε hε s).1 hmem
  · have h1 := DFunLike.congr_fun hrefl (halfSpaceOneLift x)
    have hcoord : (halfSpaceOneLift x).1 0 = x := by
      rw [halfSpaceOneLift_coordinate, max_eq_left hx.le]
    rw [halfLineTransport_apply, refl_apply_halfSpace, hcoord] at h1
    have h2 : halfSpaceOneLift (prescribedFlow ε hε s x) = halfSpaceOneLift x := h1
    have h3 : max (prescribedFlow ε hε s x) 0 = x := by
      have := congrArg (fun z : EuclideanHalfSpace 1 => z.1 0) h2
      simpa only [halfSpaceOneLift_coordinate, hcoord] using this
    rcases le_or_gt (prescribedFlow ε hε s x) 0 with hc | hc
    · rw [max_eq_right hc] at h3
      linarith
    · rwa [max_eq_left hc.le] at h3

private theorem halfLineTransport_eqOn_ge (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    Set.EqOn (halfLineTransport ε hε s) id {t : EuclideanHalfSpace 1 | ε ≤ t.1 0} ∧
      Set.EqOn (halfLineTransport ε hε s).symm id {t : EuclideanHalfSpace 1 | ε ≤ t.1 0} := by
  have hmem_of {t : EuclideanHalfSpace 1} (ht : ε ≤ t.1 0) :
      t.1 0 ∉ tsupport (prescribedField ε) := by
    intro hmem
    have hb := prescribedField_tsupport_subset hε hmem
    rw [Set.mem_Icc] at hb
    linarith [hb.2, ht, hε]
  constructor
  · intro t ht
    rw [halfLineTransport_apply]
    rw [(prescribedFlow_eqOn_compl ε hε s).1 (hmem_of ht), id_eq,
      halfSpaceOneLift_eq_self_apply t]
    rfl
  · intro t ht
    rw [halfLineTransport_symm_apply]
    rw [(prescribedFlow_eqOn_compl ε hε (-s)).1 (hmem_of ht), id_eq,
      halfSpaceOneLift_eq_self_apply t]
    rfl

theorem exists_supported_halfLine_diffeomorphism (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) ∞,
      ψ ≠ Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞ ∧
      Set.EqOn ψ id {t : EuclideanHalfSpace 1 | t.1 0 ≤ ε / 4} ∧
      Set.EqOn ψ id {t : EuclideanHalfSpace 1 | ε ≤ t.1 0} ∧
      Set.EqOn ψ.symm id {t : EuclideanHalfSpace 1 | ε ≤ t.1 0} := by
  obtain ⟨s, hs⟩ := exists_prescribedFlow_ne_refl ε hε
  refine ⟨halfLineTransport ε hε s, halfLineTransport_ne_refl hε hs, ?_,
    (halfLineTransport_eqOn_ge ε hε s).1, (halfLineTransport_eqOn_ge ε hε s).2⟩
  intro t ht
  rw [halfLineTransport_apply]
  rw [prescribedFlow_eq_self_of_le hε s ht, halfSpaceOneLift_eq_self_apply t]
  rfl

noncomputable def listTransDiffeomorph {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] :
    List (Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞) →
      Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞
  | [] => Diffeomorph.refl (𝓡∂ 3) M ∞
  | Φ :: l => Φ.trans (listTransDiffeomorph l)

theorem eqOn_listTransDiffeomorph_of_eqOn_id {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (l : List (Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞)) {K : Set M}
    (h : ∀ Φ ∈ l, Set.EqOn Φ id Kᶜ) :
    Set.EqOn (listTransDiffeomorph l) id Kᶜ ∧
      Set.EqOn (listTransDiffeomorph l).symm id Kᶜ := by
  induction l with
  | nil =>
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons Φ l ih =>
    obtain ⟨hl, hli⟩ := ih (fun Ψ hΨ => h Ψ (List.mem_cons_of_mem Φ hΨ))
    have hΦ : Set.EqOn Φ id Kᶜ := h Φ List.mem_cons_self
    have hcomp : Set.EqOn (Φ.trans (listTransDiffeomorph l)) id Kᶜ := by
      intro x hx
      change (listTransDiffeomorph l) (Φ x) = x
      rw [hΦ hx]
      exact hl hx
    have hgoal : listTransDiffeomorph (Φ :: l) = Φ.trans (listTransDiffeomorph l) := rfl
    refine ⟨by rw [hgoal]; exact hcomp, ?_⟩
    intro x hx
    have h1 : (Φ.trans (listTransDiffeomorph l)) x = x := hcomp hx
    rw [hgoal]
    calc (Φ.trans (listTransDiffeomorph l)).symm x
        = (Φ.trans (listTransDiffeomorph l)).symm ((Φ.trans (listTransDiffeomorph l)) x) := by
          rw [h1]
      _ = x := Diffeomorph.symm_apply_apply _ x

private abbrev SphereTwo : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private abbrev ModelSpace : Type := SphereTwo × EuclideanHalfSpace 1

private theorem instT2SpaceHalfSpaceOne : T2Space (EuclideanHalfSpace 1) :=
  T2Space.of_injective_continuous (f := Subtype.val) Subtype.val_injective continuous_subtype_val

private theorem instSigmaCompactSpaceHalfSpaceOne : SigmaCompactSpace (EuclideanHalfSpace 1) :=
  IsClosed.sigmaCompactSpace
    (isClosed_Ici.preimage (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous)

attribute [local instance] instT2SpaceHalfSpaceOne instSigmaCompactSpaceHalfSpaceOne
attribute [local instance] DifferentialGeometry.Manifold.euclideanHalfSpaceProdChartedSpace

private theorem modelSpace_isManifold : IsManifold (𝓡∂ 3) ∞ ModelSpace :=
  DifferentialGeometry.Manifold.euclideanHalfSpaceProd_isManifold ModelSpace

attribute [local instance] modelSpace_isManifold

private noncomputable def modelIdentity :
    PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ModelSpace ModelSpace ∞ where
  toPartialEquiv := PartialEquiv.refl ModelSpace
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun :=
    (DifferentialGeometry.Manifold.contMDiffOn_chartedSpaceTransHomeomorph_iff
      (I := (𝓡 2).prod (𝓡∂ 1)) (J := 𝓡∂ 3)
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
      (I₀ := (𝓡 2).prod (𝓡∂ 1))).mpr contMDiff_id.contMDiffOn
  contMDiffOn_invFun :=
    (DifferentialGeometry.Manifold.contMDiffOn_chartedSpaceTransHomeomorph_iff
      (I := (𝓡 2).prod (𝓡∂ 1)) (J := 𝓡∂ 3)
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
      (I₀ := 𝓡∂ 3)).mp contMDiff_id.contMDiffOn

private noncomputable def modelProductDiffeomorph (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ModelSpace ModelSpace ∞
    where
  toEquiv := Equiv.prodCongr (Equiv.refl SphereTwo) (halfLineTransport ε hε s).toEquiv
  contMDiff_toFun := contMDiff_fst.prodMk
    ((halfLineTransport ε hε s).contMDiff_toFun.comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    ((halfLineTransport ε hε s).symm.contMDiff_toFun.comp contMDiff_snd)

private theorem modelProductDiffeomorph_contMDiff (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (modelProductDiffeomorph ε hε s) := by
  have h₁ : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞
      (modelProductDiffeomorph ε hε s) :=
    (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (I := (𝓡 2).prod (𝓡∂ 1)) (J := 𝓡∂ 3)
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
      (I₀ := (𝓡 2).prod (𝓡∂ 1))).mpr
        (modelProductDiffeomorph ε hε s).contMDiff_toFun
  have hid : ContMDiff (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (id : ModelSpace → ModelSpace) :=
    contMDiffOn_univ.mp modelIdentity.contMDiffOn_invFun
  simpa only [Function.comp_id] using h₁.comp hid

private theorem modelProductDiffeomorph_contMDiff_symm (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (modelProductDiffeomorph ε hε s).symm := by
  have h₁ : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞
      (modelProductDiffeomorph ε hε s).symm :=
    (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (I := (𝓡 2).prod (𝓡∂ 1)) (J := 𝓡∂ 3)
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
      (I₀ := (𝓡 2).prod (𝓡∂ 1))).mpr
        (modelProductDiffeomorph ε hε s).contMDiff_invFun
  have hid : ContMDiff (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (id : ModelSpace → ModelSpace) :=
    contMDiffOn_univ.mp modelIdentity.contMDiffOn_invFun
  simpa only [Function.comp_id] using h₁.comp hid

private noncomputable def modelStraighteningDiffeomorph (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) ModelSpace ModelSpace ∞ where
  toEquiv := (modelProductDiffeomorph ε hε s).toEquiv
  contMDiff_toFun := modelProductDiffeomorph_contMDiff ε hε s
  contMDiff_invFun := modelProductDiffeomorph_contMDiff_symm ε hε s

private noncomputable def prescribedSupportCollar (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ModelSpace ModelSpace ∞ where
  toPartialEquiv := (modelProductDiffeomorph ε hε s).toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞
      (modelProductDiffeomorph ε hε s) univ
    have hid : ContMDiffOn ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞
        (id : ModelSpace → ModelSpace) univ :=
      modelIdentity.contMDiffOn_toFun
    have h2 : ContMDiffOn ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
        (modelProductDiffeomorph ε hε s) univ :=
      (modelProductDiffeomorph ε hε s).contMDiff_toFun.contMDiffOn
    simpa only [Function.id_comp] using hid.comp h2 (fun x _ => mem_univ _)
  contMDiffOn_invFun := by
    change ContMDiffOn (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (modelProductDiffeomorph ε hε s).symm univ
    have hid : ContMDiffOn (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞
        (id : ModelSpace → ModelSpace) univ :=
      modelIdentity.contMDiffOn_invFun
    have h2 : ContMDiffOn ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
        (modelProductDiffeomorph ε hε s).symm univ :=
      (modelProductDiffeomorph ε hε s).contMDiff_invFun.contMDiffOn
    simpa only [Function.comp_id] using h2.comp hid (fun x _ => mem_univ _)

private theorem modelIdentity_apply (q : ModelSpace) : modelIdentity q = q := rfl

private theorem modelProductDiffeomorph_apply (ε : ℝ) (hε : 0 < ε) (s : ℝ) (q : ModelSpace) :
    modelProductDiffeomorph ε hε s q = (q.1, halfLineTransport ε hε s q.2) := rfl

private theorem modelStraighteningDiffeomorph_apply (ε : ℝ) (hε : 0 < ε) (s : ℝ)
    (q : ModelSpace) :
    modelStraighteningDiffeomorph ε hε s q = (q.1, halfLineTransport ε hε s q.2) := rfl

private theorem prescribedSupportCollar_apply (ε : ℝ) (hε : 0 < ε) (s : ℝ) (q : ModelSpace) :
    prescribedSupportCollar ε hε s q = (q.1, halfLineTransport ε hε s q.2) := rfl

private theorem refl_apply_modelSpace (q : ModelSpace) :
    (Diffeomorph.refl (𝓡∂ 3) ModelSpace ∞) q = q := rfl

private theorem sphereTwoBasePoint_mem :
    EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  simp

private def sphereTwoBasePoint : SphereTwo :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), sphereTwoBasePoint_mem⟩

private theorem zero_mem_boundary_halfSpaceOne :
    (0 : EuclideanHalfSpace 1) ∈ (𝓡∂ 1).boundary (EuclideanHalfSpace 1) := by
  change (Subtype.val (0 : EuclideanHalfSpace 1)) ∈ frontier (range Subtype.val)
  rw [range_euclideanHalfSpace, frontier_halfSpace]
  rfl

private theorem modelSpace_zero_mem_boundary (p : SphereTwo) :
    ((p, (0 : EuclideanHalfSpace 1)) : ModelSpace) ∈ (𝓡∂ 3).boundary ModelSpace := by
  rw [DifferentialGeometry.Manifold.euclideanHalfSpaceProd_boundary ModelSpace,
    ModelWithCorners.boundary_prod]
  exact Or.inl ⟨mem_univ _, zero_mem_boundary_halfSpaceOne⟩

private theorem halfLineTransport_zero {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    halfLineTransport ε hε s (0 : EuclideanHalfSpace 1) = 0 := by
  rw [halfLineTransport_apply, show ((0 : EuclideanHalfSpace 1).1 0) = 0 from rfl,
    prescribedFlow_eq_self_of_le hε s (by linarith : (0 : ℝ) ≤ ε / 4)]
  exact halfSpaceOneLift_eq_self_apply 0

private theorem modelStraighteningDiffeomorph_eqOn (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    Set.EqOn (modelStraighteningDiffeomorph ε hε s) id
      (modelIdentity '' {q : ModelSpace | q.2.1 0 < ε})ᶜ := by
  rintro q hq
  rw [modelStraighteningDiffeomorph_apply]
  have hq' : ¬ (q.2.1 0 < ε) := by
    intro h
    exact hq ⟨q, h, rfl⟩
  have hge : ε ≤ q.2.1 0 := not_lt.mp hq'
  exact Prod.ext rfl ((halfLineTransport_eqOn_ge ε hε s).1 hge)

theorem exists_prescribedSupport_straightening_model (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ModelSpace ModelSpace ∞)
      (Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) ModelSpace ModelSpace ∞),
      c ≠ modelIdentity ∧ Φ ≠ Diffeomorph.refl (𝓡∂ 3) ModelSpace ∞ ∧
      (∀ p : SphereTwo, ((p, (0 : EuclideanHalfSpace 1)) : ModelSpace) ∈ c.source) ∧
      (∀ p : SphereTwo, c (p, (0 : EuclideanHalfSpace 1)) = modelIdentity (p, 0)) ∧
      (∀ p : SphereTwo, modelIdentity (p, (0 : EuclideanHalfSpace 1)) ∈
        (𝓡∂ 3).boundary ModelSpace) ∧
      (∀ (p : SphereTwo) (t : EuclideanHalfSpace 1), Φ (modelIdentity (p, t)) = c (p, t)) ∧
      Set.EqOn Φ id (modelIdentity '' {q : ModelSpace | q.2.1 0 < ε})ᶜ := by
  obtain ⟨s, hs⟩ := exists_prescribedFlow_ne_refl ε hε
  have hψ : halfLineTransport ε hε s ≠
      Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞ :=
    halfLineTransport_ne_refl hε hs
  obtain ⟨t, ht⟩ : ∃ t : EuclideanHalfSpace 1, halfLineTransport ε hε s t ≠ t := by
    by_contra h
    push Not at h
    exact hψ (Diffeomorph.ext h)
  refine ⟨prescribedSupportCollar ε hε s, modelStraighteningDiffeomorph ε hε s,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    have h1 := congrArg (fun f => f ((sphereTwoBasePoint, t) : ModelSpace)) hc
    rw [prescribedSupportCollar_apply, modelIdentity_apply] at h1
    exact ht (congrArg Prod.snd h1)
  · intro hΦ
    have h := DFunLike.congr_fun hΦ (sphereTwoBasePoint, t)
    rw [modelStraighteningDiffeomorph_apply, refl_apply_modelSpace] at h
    exact ht (congrArg Prod.snd h)
  · intro p
    exact mem_univ _
  · intro p
    rw [prescribedSupportCollar_apply, modelIdentity_apply, halfLineTransport_zero hε s]
  · intro p
    rw [modelIdentity_apply]
    exact modelSpace_zero_mem_boundary p
  · intro p t
    rw [modelIdentity_apply, modelStraighteningDiffeomorph_apply, prescribedSupportCollar_apply]
  · exact modelStraighteningDiffeomorph_eqOn ε hε s

theorem exists_prescribedSupport_straightening_model_width (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ∃ (c : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ModelSpace ModelSpace ∞)
        (Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) ModelSpace ModelSpace ∞),
        (∀ (p : SphereTwo) (t : EuclideanHalfSpace 1), t.1 0 < δ →
          Φ (modelIdentity (p, t)) = c (p, t)) ∧
        Set.EqOn Φ id (modelIdentity '' {q : ModelSpace | q.2.1 0 < ε})ᶜ := by
  obtain ⟨s, _⟩ := exists_prescribedFlow_ne_refl ε hε
  exact ⟨ε, hε, le_rfl, prescribedSupportCollar ε hε s,
    modelStraighteningDiffeomorph ε hε s,
    fun p t _ => by
      rw [modelIdentity_apply, modelStraighteningDiffeomorph_apply, prescribedSupportCollar_apply],
    modelStraighteningDiffeomorph_eqOn ε hε s⟩

end DifferentialGeometry.Topology.Collar
