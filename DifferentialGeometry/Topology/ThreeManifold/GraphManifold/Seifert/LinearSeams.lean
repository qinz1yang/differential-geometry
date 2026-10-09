import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitSphere
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SupportedExtension
import DifferentialGeometry.Topology.Manifold.HalfLine

/-!
# Linear seams

Lane LS, for the normalization moves of `Seifert/Normalize.lean`. A seam `j` of an elementary
presentation is linear (`IsLinearSeam`) when its matching, the gluing map in the collar
coordinates of the two sides, is `linearTorusDiffeomorph` of its own `torusUnit`;
`HasLinearSeams` asks this of every seam.

Literal facts (tier 1). `crossMap j b` carries the port coordinates of side `b` to those of side
`!b` (the matching or its inverse), with matrix `crossUnit j b`, and `fillingDistance j b` is
`|crossUnit j b 0 0|` (`delta_smul_meridianSlope`). For the solid torus on side `b`,
`meridianCircle j b w` is the boundary circle of the meridian disc at fibre coordinate `w` and
`hostFibre j b s` the fibre of the host over the boundary point of its base at `s`, both in `W`.
For a linear seam at distance `0` each meridian circle is exactly one host fibre and each host
fibre is exactly one meridian circle (`IsLinearSeam.meridianCircle_eq_hostFibre`,
`exists_hostFibre_eq_meridianCircle`); at distance `1` a meridian circle meets every host fibre
in exactly one point (`existsUnique_mem_hostFibre`).

Linearization (tier 2). By `TorusMappingClassLinear` the matching `f` is isotopic to its linear
map `L` through `F` (`linearIsotopy`). With the cutoff `seamCut` (`0` below `1/4`, `1` above
`1/2`) the right half collar of the seam is reparametrized by
`(y, s) ↦ (F (seamCut s) (L⁻¹ y), s)` (`collarSlice`), which is `f ∘ L⁻¹` near the torus and the
identity from height `1/2` on; the seam chart is precomposed with the matching slice
diffeomorphism `seamSlice`. The cut carrier, its pieces, the gluing, the reconstruction of `W`,
the left collars, the external collars and the seam regions are unchanged
(`linearPresentation`); the new matching is `L`. The product structure of each piece is
corrected by a diffeomorphism of the piece supported in the collars of its right seam sides
(`exists_chartTwist`, `exists_multiTwist`, from `exists_diffeomorph_family_extension`), so the
bases and ports stay the same (`linearPiece`). `ElementaryPresentation.linearize` therefore
has linear seams, the same count, pieces, kinds, slopes, filling distances and move
predicates (`isSplitSeam_linearize`, `isMergeSeam_linearize`, `isMoveFree_linearize`), and
`exists_hasLinearSeams` packages this.

The split sphere (tier 3, partial). `IsLinearSeam.seam_junction`: at distance `0` the collar of
the meridian disc at fibre `w` and the host band over the collar line through `s₀ = w ^ B₀₁`
are the two halves of one seam-chart annulus `seam j '' (C × (-1, 1))`, `C` a linear circle of
`T²`; this is where `D_a ∪ γ × S¹ ∪ D_b` is smooth across the seam. Not built: an arc `γ` of the
pants base with collar-line ends separating the other two boundary circles, a parametrization of
the disc base compatible with its collar, and the assembly of the three pieces into a smooth
embedding of the round sphere for `exists_sphereSurgery`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Twist

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N]

theorem exists_chartTwist (e : PartialDiffeomorph J I N M ∞) (D : N ≃ₘ⟮J, J⟯ N) {K : Set N}
    (hK : IsCompact K) (hKs : K ⊆ e.source) (hfix : ∀ z, z ∉ K → D z = z) :
    ∃ Θ : M ≃ₘ⟮I, I⟯ M, (∀ z, z ∈ e.source → Θ (e z) = e (D z)) ∧
      ∀ x, x ∉ e '' K → Θ x = x := by
  obtain ⟨Fam, -, -, heq, -, -, hfam⟩ := e.exists_diffeomorph_family_extension (IP := 𝓘(ℝ))
    (fun _ : ℝ => D) (D.contMDiff.comp contMDiff_snd) (D.symm.contMDiff.comp contMDiff_snd)
    hK hKs (fun _ z hz => hfix z hz)
  refine ⟨Fam 0, fun z hz => ?_, fun x hx => (hfam 0 x hx).1⟩
  classical
  rw [(heq 0 (e z)).1, OpenPartialHomeomorph.extendById]
  change (if e z ∈ e.target then e (D (e.symm (e z))) else e z) = e (D z)
  have h1 : e.symm.toPartialEquiv (e.toPartialEquiv z) = z := e.toPartialEquiv.left_inv hz
  rw [ite_eq_left (e.map_source hz), h1]

theorem exists_multiTwist {k : ℕ} (e : Fin k → PartialDiffeomorph J I N M ∞) {S K : Set N}
    (hsrc : ∀ m, (e m).source = S)
    (hdisj : Pairwise fun m m' => Disjoint (e m).target (e m').target)
    (D : Fin k → N ≃ₘ⟮J, J⟯ N) (hK : IsCompact K) (hKS : K ⊆ S)
    (hfix : ∀ m z, z ∉ K → D m z = z) (hS : ∀ m z, z ∈ S → D m z ∈ S) :
    ∃ Θ : M ≃ₘ⟮I, I⟯ M, ∀ m z, z ∈ S → Θ (e m z) = e m (D m z) := by
  classical
  have key : ∀ l : List (Fin k), l.Nodup → ∃ Θ : M ≃ₘ⟮I, I⟯ M,
      ∀ m z, z ∈ S → Θ (e m z) = if m ∈ l then e m (D m z) else e m z := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨Diffeomorph.refl I M ∞, fun m z _ => by simp⟩
    | cons a l ih =>
      intro hl
      obtain ⟨Θ, hΘ⟩ := ih (List.nodup_cons.mp hl).2
      obtain ⟨τ, hτ, hτfix⟩ := exists_chartTwist (e a) (D a) hK ((hsrc a).symm ▸ hKS) (hfix a)
      refine ⟨τ.trans Θ, fun m z hz => ?_⟩
      rw [Diffeomorph.coe_trans, Function.comp_apply]
      by_cases hma : m = a
      · subst hma
        rw [hτ z ((hsrc m).symm ▸ hz), hΘ m _ (hS m z hz), ite_eq_right (List.nodup_cons.mp hl).1,
          ite_eq_left List.mem_cons_self]
      · have hne : e m z ∉ e a '' K := by
          rintro ⟨y, hy, hya⟩
          exact Set.disjoint_left.mp (hdisj hma) ((e m).map_source ((hsrc m).symm ▸ hz))
            (hya ▸ (e a).map_source ((hsrc a).symm ▸ hKS hy))
        rw [hτfix _ hne, hΘ m z hz]
        simp only [List.mem_cons, hma, false_or]
  obtain ⟨Θ, hΘ⟩ := key (List.finRange k) (List.nodup_finRange k)
  exact ⟨Θ, fun m z hz => by rw [hΘ m z hz, ite_eq_left (List.mem_finRange m)]⟩

omit [T2Space M] in
theorem toPartialDiffeomorph_trans_source (D : N ≃ₘ⟮J, J⟯ N) (e : PartialDiffeomorph J I N M ∞) :
    (D.toPartialDiffeomorph.trans e).source = D ⁻¹' e.source := by
  rw [PartialDiffeomorph.trans_source]
  exact Set.univ_inter _

omit [T2Space M] in
theorem toPartialDiffeomorph_trans_target (D : N ≃ₘ⟮J, J⟯ N) (e : PartialDiffeomorph J I N M ∞) :
    (D.toPartialDiffeomorph.trans e).target = e.target := by
  change (D.toPartialDiffeomorph.toPartialEquiv.trans e.toPartialEquiv).target = e.target
  rw [PartialEquiv.trans_target]
  exact Set.inter_univ _

end Twist

section Slice

variable {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] {HX : Type*}
  [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X]
  [ChartedSpace HX X]

def sliceDiffeomorph (G : ℝ → Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hG : ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞ fun q : ℝ × Torus => G q.1 q.2)
    (hG' : ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      fun q : ℝ × Torus => (G q.1).symm q.2)
    (h : X → ℝ) (hh : ContMDiff IX 𝓘(ℝ) ∞ h) :
    (Torus × X) ≃ₘ⟮torusModel.prod IX, torusModel.prod IX⟯ (Torus × X) where
  toFun p := (G (h p.2) p.1, p.2)
  invFun p := ((G (h p.2)).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun :=
    (hG.comp ((hh.comp contMDiff_snd).prodMk contMDiff_fst)).prodMk contMDiff_snd
  contMDiff_invFun :=
    (hG'.comp ((hh.comp contMDiff_snd).prodMk contMDiff_fst)).prodMk contMDiff_snd

end Slice

section LinearIsotopy

def seamCut (s : ℝ) : ℝ := Real.smoothTransition (4 * s - 1)

theorem contDiff_seamCut : ContDiff ℝ ∞ seamCut :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem seamCut_of_le {s : ℝ} (hs : s ≤ 1 / 4) : seamCut s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem seamCut_of_ge {s : ℝ} (hs : 1 / 2 ≤ s) : seamCut s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

variable (hL : TorusMappingClassLinear) (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)

def linearIsotopy : ℝ → Torus ≃ₘ⟮torusModel, torusModel⟯ Torus := (hL f).choose

theorem linearIsotopy_spec :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
        (fun q : ℝ × Torus => linearIsotopy hL f q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
        (fun q : ℝ × Torus => (linearIsotopy hL f q.1).symm q.2) ∧
      linearIsotopy hL f 0 = f ∧ linearIsotopy hL f 1 = linearTorusDiffeomorph (torusUnit f) :=
  (hL f).choose_spec

def collarTwist (t : ℝ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (linearTorusDiffeomorph (torusUnit f)).symm.trans (linearIsotopy hL f (seamCut t))

def seamTwist (t : ℝ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (linearIsotopy hL f (seamCut t)).trans f.symm

private theorem contMDiff_isotopy_cut :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => linearIsotopy hL f (seamCut q.1) q.2) :=
  (linearIsotopy_spec hL f).1.comp
    ((contDiff_seamCut.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)

private theorem contMDiff_isotopy_cut_symm :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => (linearIsotopy hL f (seamCut q.1)).symm q.2) :=
  (linearIsotopy_spec hL f).2.1.comp
    ((contDiff_seamCut.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)

theorem contMDiff_collarTwist :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => collarTwist hL f q.1 q.2) :=
  (contMDiff_isotopy_cut hL f).comp
    (contMDiff_fst.prodMk ((linearTorusDiffeomorph (torusUnit f)).symm.contMDiff.comp
      contMDiff_snd))

theorem contMDiff_collarTwist_symm :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => (collarTwist hL f q.1).symm q.2) :=
  (linearTorusDiffeomorph (torusUnit f)).contMDiff.comp (contMDiff_isotopy_cut_symm hL f)

theorem contMDiff_seamTwist :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => seamTwist hL f q.1 q.2) :=
  f.symm.contMDiff.comp (contMDiff_isotopy_cut hL f)

theorem contMDiff_seamTwist_symm :
    ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => (seamTwist hL f q.1).symm q.2) :=
  (contMDiff_isotopy_cut_symm hL f).comp (contMDiff_fst.prodMk (f.contMDiff.comp contMDiff_snd))

theorem collarTwist_apply_linear {t : ℝ} (ht : t ≤ 1 / 4) (y : Torus) :
    collarTwist hL f t (linearTorusDiffeomorph (torusUnit f) y) = f y := by
  change linearIsotopy hL f (seamCut t) ((linearTorusDiffeomorph (torusUnit f)).symm
    (linearTorusDiffeomorph (torusUnit f) y)) = f y
  rw [Diffeomorph.symm_apply_apply, seamCut_of_le ht, (linearIsotopy_spec hL f).2.2.1]

theorem collarTwist_of_ge {t : ℝ} (ht : 1 / 2 ≤ t) (y : Torus) : collarTwist hL f t y = y := by
  change linearIsotopy hL f (seamCut t) ((linearTorusDiffeomorph (torusUnit f)).symm y) = y
  rw [seamCut_of_ge ht, (linearIsotopy_spec hL f).2.2.2, Diffeomorph.apply_symm_apply]

theorem seamTwist_of_le {t : ℝ} (ht : t ≤ 1 / 4) (y : Torus) : seamTwist hL f t y = y := by
  change f.symm (linearIsotopy hL f (seamCut t) y) = y
  rw [seamCut_of_le ht, (linearIsotopy_spec hL f).2.2.1, Diffeomorph.symm_apply_apply]

theorem apply_seamTwist (t : ℝ) (y : Torus) :
    f (seamTwist hL f t y) = collarTwist hL f t (linearTorusDiffeomorph (torusUnit f) y) := by
  change f (f.symm (linearIsotopy hL f (seamCut t) y)) = linearIsotopy hL f (seamCut t)
    ((linearTorusDiffeomorph (torusUnit f)).symm (linearTorusDiffeomorph (torusUnit f) y))
  rw [Diffeomorph.apply_symm_apply, Diffeomorph.symm_apply_apply]

def collarSlice : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
    (Torus × EuclideanHalfSpace 1) :=
  sliceDiffeomorph (collarTwist hL f) (contMDiff_collarTwist hL f)
    (contMDiff_collarTwist_symm hL f) (fun s : EuclideanHalfSpace 1 => s.1 0)
    contMDiff_halfSpaceOneCoordinate

theorem collarSlice_apply (p : Torus × EuclideanHalfSpace 1) :
    collarSlice hL f p = (collarTwist hL f (p.2.1 0) p.1, p.2) := rfl

def seamSlice : (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) :=
  sliceDiffeomorph (seamTwist hL f) (contMDiff_seamTwist hL f) (contMDiff_seamTwist_symm hL f)
    id contMDiff_id

theorem seamSlice_apply (p : Torus × ℝ) : seamSlice hL f p = (seamTwist hL f p.2 p.1, p.2) :=
  rfl

end LinearIsotopy

theorem reversesBoundaryOrientation_congr {C : CompactCarrier.{u}}
    {l r r' : Torus × EuclideanHalfSpace 1 → C.Carrier} (h : ReversesBoundaryOrientation C l r)
    (hr : ∀ t : Torus, r' =ᶠ[𝓝 (t, halfZero)] r) : ReversesBoundaryOrientation C l r' := by
  intro t
  obtain ⟨L, R, hL, hR, hLR⟩ := h t
  have key : ∀ y, y = r (t, halfZero) →
      ∃ R' : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ] TangentSpace C.model y,
        (∀ v, R' v = R v) ∧
        Orientation.map (Fin 3) L.symm (C.orientation.orientation (l (t, halfZero))) =
          -Orientation.map (Fin 3) R'.symm (C.orientation.orientation y) := by
    intro y hy
    subst hy
    exact ⟨R, fun v => rfl, hLR⟩
  obtain ⟨R', hR', hLR'⟩ := key _ (hr t).self_of_nhds
  refine ⟨L, R', hL, fun v => ?_, hLR'⟩
  rw [hR' v, hR v, (hr t).mfderiv_eq]
  rfl

theorem isOpen_halfCollar_lt (a : ℝ) :
    IsOpen {p : Torus × EuclideanHalfSpace 1 | p.2.1 0 < a} :=
  isOpen_lt (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const

private theorem halfSpaceOneLift_val (h : EuclideanHalfSpace 1) : halfSpaceOneLift (h.1 0) = h := by
  rw [halfSpaceOneLift_eq]
  have he : (⟨max 0 (h.1 0), mem_Ici.mpr (le_max_left _ _)⟩ : Ici (0 : ℝ)) =
      halfSpaceOneHomeomorph h :=
    Subtype.ext (max_eq_right h.2)
  rw [he]
  exact halfSpaceOneHomeomorph.symm_apply_apply h

theorem isCompact_halfCollar_half :
    IsCompact {q : Torus × EuclideanHalfSpace 1 | q.2.1 0 ≤ 1 / 2} := by
  have hc : IsCompact ((univ : Set Torus) ×ˢ (halfSpaceOneLift '' Icc 0 (1 / 2))) :=
    isCompact_univ.prod (isCompact_Icc.image_of_continuousOn
      (contMDiffOn_halfSpaceOneLift.continuousOn.mono Icc_subset_Ici_self))
  exact hc.of_isClosed_subset (isClosed_le (contMDiff_halfSpaceOneCoordinate.continuous.comp
    continuous_snd) continuous_const) fun q hq =>
      ⟨mem_univ _, q.2.1 0, ⟨q.2.2, hq⟩, halfSpaceOneLift_val q.2⟩

section Linearize

variable (hL : TorusMappingClassLinear)

def linearPairing {C : CompactCarrier.{u}} (P : TorusPairing C) : TorusPairing C where
  count := P.count
  gluing := P.gluing
  leftParam := P.leftParam
  rightParam j := (collarTwist hL (P.matching j) 0).toHomeomorph.trans (P.rightParam j)
  matching j := linearTorusDiffeomorph (torusUnit (P.matching j))
  matching_eq j t := by
    rw [P.matching_eq j t]
    exact congrArg (P.rightParam j)
      (collarTwist_apply_linear hL (P.matching j) (by norm_num) t).symm
  leftCollar := P.leftCollar
  rightCollar j := (collarSlice hL (P.matching j)).toPartialDiffeomorph.trans (P.rightCollar j)
  left_source := P.left_source
  right_source j := by
    rw [toPartialDiffeomorph_trans_source, P.right_source j]
    rfl
  left_zero := P.left_zero
  right_zero j t := P.right_zero j _
  reversing j := reversesBoundaryOrientation_congr (P.reversing j) fun t => by
    filter_upwards [(isOpen_halfCollar_lt (1 / 4)).mem_nhds
      (show (t, halfZero).2.1 0 < 1 / 4 by change (0 : ℝ) < 1 / 4; norm_num)] with p hp
    change P.rightCollar j (collarTwist hL (P.matching j) (p.2.1 0)
      (linearTorusDiffeomorph (torusUnit (P.matching j)) p.1), p.2) =
        P.rightCollar j (P.matching j p.1, p.2)
    rw [collarTwist_apply_linear hL (P.matching j) (le_of_lt hp)]

variable {W : CompactCarrier.{u}}

def linearPresentation (T : TorusPresentation W) : TorusPresentation W where
  cutCarrier := T.cutCarrier
  components := T.components
  pairing := linearPairing hL T.pairing
  externalCount := T.externalCount
  external := T.external
  cutExternal := T.cutExternal
  external_exhausted := T.external_exhausted
  cut_boundary_exhausted := T.cut_boundary_exhausted
  external_disjoint := T.external_disjoint
  reconstruction := T.reconstruction
  quotient_smooth := T.quotient_smooth
  quotient_oriented := T.quotient_oriented
  interiorImage := T.interiorImage
  interiorDiffeomorph := T.interiorDiffeomorph
  interior_map := T.interior_map
  seam j := (seamSlice hL (T.pairing.matching j)).toPartialDiffeomorph.trans (T.seam j)
  seam_source j := by
    rw [toPartialDiffeomorph_trans_source, T.seam_source j]
    rfl
  seam_zero j t := by
    change T.seam j (seamTwist hL (T.pairing.matching j) 0 t, 0) = _
    rw [seamTwist_of_le hL _ (by norm_num)]
    exact T.seam_zero j t
  seam_positive j t s hs hs1 := by
    change T.seam j (seamTwist hL (T.pairing.matching j) s t, s) =
      T.reconstruction (T.pairing.quotientMap (T.pairing.rightCollar j
        (collarTwist hL (T.pairing.matching j) s
          (linearTorusDiffeomorph (torusUnit (T.pairing.matching j)) t), halfPoint s hs)))
    rw [T.seam_positive j _ s hs hs1, apply_seamTwist]
  seam_negative j t s hs hs1 := by
    change T.seam j (seamTwist hL (T.pairing.matching j) s t, s) = _
    rw [seamTwist_of_le hL _ (by linarith)]
    exact T.seam_negative j t s hs hs1
  seam_interior j := (le_of_eq (toPartialDiffeomorph_trans_target _ _)).trans (T.seam_interior j)
  seam_disjoint i j hij := Disjoint.mono (le_of_eq (toPartialDiffeomorph_trans_target _ _))
    (le_of_eq (toPartialDiffeomorph_trans_target _ _)) (T.seam_disjoint hij)
  marked_collar := T.marked_collar
  external_seam_disjoint i j := Disjoint.mono le_rfl
    (le_of_eq (toPartialDiffeomorph_trans_target _ _)) (T.external_seam_disjoint i j)
  leftPiece := T.leftPiece
  rightPiece := T.rightPiece
  left_owned := T.left_owned
  right_owned := T.right_owned
  externalPiece := T.externalPiece
  external_owned := T.external_owned

def sideTwist (T : TorusPresentation W) : T.Side →
    (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1)
  | .inl _ => Diffeomorph.refl _ _ _
  | .inr (.inl j) => collarSlice hL (T.pairing.matching j)
  | .inr (.inr _) => Diffeomorph.refl _ _ _

theorem sideTwist_snd (T : TorusPresentation W) :
    ∀ (s : T.Side) (p : Torus × EuclideanHalfSpace 1), (sideTwist hL T s p).2 = p.2
  | .inl _, _ => rfl
  | .inr (.inl _), _ => rfl
  | .inr (.inr _), _ => rfl

theorem sideTwist_of_half_lt (T : TorusPresentation W) :
    ∀ (s : T.Side) (p : Torus × EuclideanHalfSpace 1), 1 / 2 < p.2.1 0 → sideTwist hL T s p = p
  | .inl _, _, _ => rfl
  | .inr (.inl j), p, hp =>
    Prod.ext (collarTwist_of_ge hL (T.pairing.matching j) hp.le p.1) rfl
  | .inr (.inr _), _, _ => rfl

theorem sideCollar_linearPresentation (T : TorusPresentation W) :
    ∀ (s : T.Side) (p : Torus × EuclideanHalfSpace 1),
      (linearPresentation hL T).sideCollar s p = T.sideCollar s (sideTwist hL T s p)
  | .inl _, _ => rfl
  | .inr (.inl _), _ => rfl
  | .inr (.inr _), _ => rfl

theorem exists_pieceTwist (T : TorusPresentation W) (i : Fin T.components.count) {k : ℕ}
    (port : Fin k ≃ T.OwnedSide i) :
    ∃ Θ : T.components.piece i ≃ₘ⟮T.cutCarrier.model, T.cutCarrier.model⟯ T.components.piece i,
      ∀ m z, z ∈ halfCollarSource →
        Θ (T.pieceCollar i (port m) z) = T.pieceCollar i (port m) (sideTwist hL T (port m).1 z) :=
  exists_multiTwist (fun m => T.pieceCollar i (port m)) (fun m => T.pieceCollar_source i _)
    (fun m m' hm => Disjoint.mono (le_of_eq (T.pieceCollar_target i _))
      (le_of_eq (T.pieceCollar_target i _))
      ((T.sideCollar_disjoint fun h => hm (port.injective (Subtype.ext h))).preimage _))
    (fun m => sideTwist hL T (port m).1) isCompact_halfCollar_half
    (fun z hz => show z.2.1 0 < 1 from lt_of_le_of_lt hz (by norm_num))
    (fun m z hz => sideTwist_of_half_lt hL T _ z (lt_of_not_ge hz))
    (fun m z hz => by
      change (sideTwist hL T (port m).1 z).2.1 0 < 1
      rw [sideTwist_snd]
      exact hz)

def pieceTwist (T : TorusPresentation W) (i : Fin T.components.count) {k : ℕ}
    (port : Fin k ≃ T.OwnedSide i) :
    T.components.piece i ≃ₘ⟮T.cutCarrier.model, T.cutCarrier.model⟯ T.components.piece i :=
  (exists_pieceTwist hL T i port).choose

theorem pieceTwist_pieceCollar (T : TorusPresentation W) (i : Fin T.components.count) {k : ℕ}
    (port : Fin k ≃ T.OwnedSide i) (m : Fin k) {z : Torus × EuclideanHalfSpace 1}
    (hz : z ∈ halfCollarSource) :
    pieceTwist hL T i port (T.pieceCollar i (port m) z) =
      T.pieceCollar i (port m) (sideTwist hL T (port m).1 z) :=
  (exists_pieceTwist hL T i port).choose_spec m z hz

def ownedSideLinear (T : TorusPresentation W) (i : Fin T.components.count) :
    T.OwnedSide i ≃ (linearPresentation hL T).OwnedSide i :=
  Equiv.subtypeEquivRight fun s => by rcases s with k | k | k <;> exact Iff.rfl

theorem ownedSideLinear_val (T : TorusPresentation W) (i : Fin T.components.count)
    (s : T.OwnedSide i) : (ownedSideLinear hL T i s).val = s.val := rfl

def linearPiece {T : TorusPresentation W} {i : Fin T.components.count} {k : ℕ}
    (P : ProductFibredPiece T i k) : ProductFibredPiece (linearPresentation hL T) i k where
  base := P.base
  port := P.port.trans (ownedSideLinear hL T i)
  trivialization := P.trivialization.trans (pieceTwist hL T i P.port)
  collar_eq m p hp := by
    have hs : sideTwist hL T (P.port m).1 p ∈ halfCollarSource := by
      change (sideTwist hL T (P.port m).1 p).2.1 0 < 1
      rw [sideTwist_snd]
      exact hp
    apply Subtype.ext
    refine (TorusPresentation.pieceCollar_apply (linearPresentation hL T) i _ hp).trans ?_
    refine (sideCollar_linearPresentation hL T _ p).trans ?_
    refine (TorusPresentation.pieceCollar_apply T i (P.port m) hs).symm.trans ?_
    rw [← pieceTwist_pieceCollar hL T i P.port m hp, P.collar_eq m p hp]
    rfl

end Linearize

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

def IsLinearSeam (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) : Prop :=
  E.toTorus.pairing.matching j = linearTorusDiffeomorph (torusUnit (E.toTorus.pairing.matching j))

def HasLinearSeams (E : ElementaryPresentation W) : Prop := ∀ j, E.IsLinearSeam j

def linearize (E : ElementaryPresentation W) (hL : TorusMappingClassLinear) :
    ElementaryPresentation W where
  toTorus := linearPresentation hL E.toTorus
  kind := E.kind
  kind_mem := E.kind_mem
  piece i := linearPiece hL (E.piece i)

variable (E : ElementaryPresentation W) (hL : TorusMappingClassLinear)

@[simp]
theorem complexity_linearize : (E.linearize hL).complexity = E.complexity := rfl

theorem linearize_matching (j : Fin E.toTorus.pairing.count) :
    (E.linearize hL).toTorus.pairing.matching j =
      linearTorusDiffeomorph (torusUnit (E.toTorus.pairing.matching j)) := rfl

theorem torusUnit_linearize_matching (j : Fin E.toTorus.pairing.count) :
    torusUnit ((E.linearize hL).toTorus.pairing.matching j) =
      torusUnit (E.toTorus.pairing.matching j) :=
  (torusUnit_eq_of_isotopic (hL _)).symm

theorem hasLinearSeams_linearize : (E.linearize hL).HasLinearSeams := fun j =>
  congrArg linearTorusDiffeomorph (E.torusUnit_linearize_matching hL j).symm

theorem seamPiece_linearize (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.linearize hL).seamPiece j b = E.seamPiece j b := by
  cases b <;> rfl

theorem fillingDistance_linearize (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.linearize hL).fillingDistance j b = E.fillingDistance j b := by
  cases b <;> simp only [fillingDistance, torusUnit_linearize_matching]

theorem isSplitSeam_linearize (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.linearize hL).IsSplitSeam j b ↔ E.IsSplitSeam j b := by
  unfold IsSplitSeam
  rw [fillingDistance_linearize]
  rfl

theorem isMergeSeam_linearize (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.linearize hL).IsMergeSeam j b ↔ E.IsMergeSeam j b := by
  unfold IsMergeSeam
  rw [fillingDistance_linearize]
  rfl

theorem isAbsorbSeam_linearize (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.linearize hL).IsAbsorbSeam j b ↔ E.IsAbsorbSeam j b := Iff.rfl

theorem isMoveFree_linearize : (E.linearize hL).IsMoveFree ↔ E.IsMoveFree := by
  constructor
  · intro h j b hj
    rcases h j b hj with h1 | ⟨h3, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h3, h2.trans_eq (E.fillingDistance_linearize hL j b)⟩
  · intro h j b hj
    rcases h j b hj with h1 | ⟨h3, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h3, h2.trans_eq (E.fillingDistance_linearize hL j b).symm⟩

theorem seam_target_linearize (j : Fin E.toTorus.pairing.count) :
    ((E.linearize hL).toTorus.seam j).target = (E.toTorus.seam j).target :=
  toPartialDiffeomorph_trans_target _ _

end ElementaryPresentation

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

theorem exists_hasLinearSeams (E : ElementaryPresentation W) (hL : TorusMappingClassLinear) :
    ∃ (E' : ElementaryPresentation W)
      (hc : E'.toTorus.pairing.count = E.toTorus.pairing.count)
      (hp : E'.toTorus.components.count = E.toTorus.components.count),
      E'.HasLinearSeams ∧ E'.toTorus.cutCarrier = E.toTorus.cutCarrier ∧
      E'.complexity = E.complexity ∧
      (∀ i, E'.kind i = E.kind (Fin.cast hp i)) ∧
      (∀ j, Fin.cast hp (E'.toTorus.leftPiece j) = E.toTorus.leftPiece (Fin.cast hc j)) ∧
      (∀ j, Fin.cast hp (E'.toTorus.rightPiece j) = E.toTorus.rightPiece (Fin.cast hc j)) ∧
      (∀ j, torusUnit (E'.toTorus.pairing.matching j) =
        torusUnit (E.toTorus.pairing.matching (Fin.cast hc j))) ∧
      (∀ j b, E'.fillingDistance j b = E.fillingDistance (Fin.cast hc j) b) ∧
      ∀ j, (E'.toTorus.seam j).target = (E.toTorus.seam (Fin.cast hc j)).target :=
  ⟨E.linearize hL, rfl, rfl, E.hasLinearSeams_linearize hL, rfl, rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, E.torusUnit_linearize_matching hL,
    E.fillingDistance_linearize hL, E.seam_target_linearize hL⟩

end ElementaryPresentation

section LinearSlopes

theorem zpow_zpow_of_unit {n : ℤ} (hn : n = 1 ∨ n = -1) (z : Circle) : (z ^ n) ^ n = z := by
  rcases hn with rfl | rfl <;> simp

theorem delta_smul_meridianSlope (B : GL (Fin 2) ℤ) :
    PrimitiveSlope.delta (B • meridianSlope) fiberSlope =
      ((B : Matrix (Fin 2) (Fin 2) ℤ) 0 0).natAbs := by
  rw [meridianSlope, fiberSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.delta_mk]
  simp [slopeDet, smulVec]

theorem units_entries_of_zero (B : GL (Fin 2) ℤ) (h : (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0) :
    ((B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 ∨ (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -1) ∧
      ((B : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 1 ∨ (B : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -1) := by
  have hd := Int.isUnit_iff.mp (Matrix.isUnits_det_units B)
  rw [Matrix.det_fin_two, h, zero_mul, zero_sub] at hd
  rcases hd with hd | hd
  · have hm : (B : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -1 := by
      linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inr h2, Or.inl h1⟩
    · exact ⟨Or.inl h2, Or.inr h1⟩
  · have hm : (B : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h2, Or.inl h1⟩
    · exact ⟨Or.inr h2, Or.inr h1⟩

theorem range_linearTorusMap_eq_fiber (B : Matrix (Fin 2) (Fin 2) ℤ) (h0 : B 0 0 = 0)
    (h1 : B 1 0 = 1 ∨ B 1 0 = -1) (w : Circle) :
    range (fun z : Circle => linearTorusMap B (z, w)) =
      range (fun v : Circle => ((w ^ B 0 1, v) : Torus)) := by
  ext ⟨a, c⟩
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ^ B 1 0 * w ^ B 1 1, ?_⟩
    rw [← hz]
    simp [linearTorusMap, h0]
  · rintro ⟨v, hv⟩
    refine ⟨(v * (w ^ B 1 1)⁻¹) ^ B 1 0, ?_⟩
    rw [← hv]
    simp only [linearTorusMap, h0, zpow_zero, one_mul, zpow_zpow_of_unit h1, inv_mul_cancel_right]

theorem existsUnique_linearTorusMap_fst (B : Matrix (Fin 2) (Fin 2) ℤ)
    (h : B 0 0 = 1 ∨ B 0 0 = -1) (w s : Circle) :
    ∃! z : Circle, (linearTorusMap B (z, w)).1 = s := by
  refine ⟨(s * (w ^ B 0 1)⁻¹) ^ B 0 0, ?_, fun z hz => ?_⟩
  · change ((s * (w ^ B 0 1)⁻¹) ^ B 0 0) ^ B 0 0 * w ^ B 0 1 = s
    rw [zpow_zpow_of_unit h, inv_mul_cancel_right]
  · change z ^ B 0 0 * w ^ B 0 1 = s at hz
    rw [← hz, mul_inv_cancel_right, zpow_zpow_of_unit h]

end LinearSlopes

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

def crossMap (j : Fin E.toTorus.pairing.count) :
    Bool → Torus ≃ₘ⟮torusModel, torusModel⟯ Torus
  | true => E.toTorus.pairing.matching j
  | false => (E.toTorus.pairing.matching j).symm

def crossUnit (j : Fin E.toTorus.pairing.count) : Bool → GL (Fin 2) ℤ
  | true => torusUnit (E.toTorus.pairing.matching j)
  | false => (torusUnit (E.toTorus.pairing.matching j))⁻¹

theorem fillingDistance_eq_crossUnit (j : Fin E.toTorus.pairing.count) :
    ∀ b, E.fillingDistance j b = PrimitiveSlope.delta (E.crossUnit j b • meridianSlope) fiberSlope
  | true => rfl
  | false => E.fillingDistance_false j

theorem IsLinearSeam.crossMap_apply {E : ElementaryPresentation W}
    {j : Fin E.toTorus.pairing.count} (h : E.IsLinearSeam j) :
    ∀ b t, E.crossMap j b t = linearTorusMap (E.crossUnit j b) t
  | true, t => congrArg (fun φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus => φ t) h
  | false, t => congrArg (fun φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus => φ.symm t) h

theorem cutMap_sideCollar_cross (j : Fin E.toTorus.pairing.count) :
    ∀ (b : Bool) (t : Torus),
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (t, halfZero)) =
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j !b) (E.crossMap j b t, halfZero))
  | true, t => by
    change E.toTorus.cutMap (E.toTorus.pairing.leftCollar j (t, halfZero)) =
      E.toTorus.cutMap (E.toTorus.pairing.rightCollar j (E.toTorus.pairing.matching j t, halfZero))
    rw [E.toTorus.cutMap_leftCollar j (zero_mem_halfCollarSource t),
      E.toTorus.cutMap_rightCollar j (zero_mem_halfCollarSource _), Diffeomorph.symm_apply_apply]
    change E.toTorus.seam j (t, -(0 : ℝ)) = E.toTorus.seam j (t, 0)
    rw [neg_zero]
  | false, t => by
    change E.toTorus.cutMap (E.toTorus.pairing.rightCollar j (t, halfZero)) =
      E.toTorus.cutMap (E.toTorus.pairing.leftCollar j
        ((E.toTorus.pairing.matching j).symm t, halfZero))
    rw [E.toTorus.cutMap_leftCollar j (zero_mem_halfCollarSource _),
      E.toTorus.cutMap_rightCollar j (zero_mem_halfCollarSource t)]
    change E.toTorus.seam j (_, (0 : ℝ)) = E.toTorus.seam j (_, -(0 : ℝ))
    rw [neg_zero]

theorem cutMap_sideCollar_seamSide_injective (j : Fin E.toTorus.pairing.count) :
    ∀ b, Function.Injective fun y : Torus =>
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (y, halfZero))
  | true, y, y', h => by
    have hm : ∀ x : Torus, (x, -(halfZero.1 0)) ∈ (E.toTorus.seam j).source := fun x => by
      rw [E.toTorus.seam_source]
      change -1 < -(0 : ℝ) ∧ -(0 : ℝ) < 1
      norm_num
    have h' := h
    simp only [seamSide] at h'
    change E.toTorus.cutMap (E.toTorus.pairing.leftCollar j (y, halfZero)) =
      E.toTorus.cutMap (E.toTorus.pairing.leftCollar j (y', halfZero)) at h'
    rw [E.toTorus.cutMap_leftCollar j (zero_mem_halfCollarSource y),
      E.toTorus.cutMap_leftCollar j (zero_mem_halfCollarSource y')] at h'
    exact congrArg Prod.fst ((E.toTorus.seam j).toPartialEquiv.injOn (hm y) (hm y') h')
  | false, y, y', h => by
    have hm : ∀ x : Torus, (x, halfZero.1 0) ∈ (E.toTorus.seam j).source := fun x => by
      rw [E.toTorus.seam_source]
      change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
      norm_num
    have h' := h
    simp only [seamSide] at h'
    change E.toTorus.cutMap (E.toTorus.pairing.rightCollar j (y, halfZero)) =
      E.toTorus.cutMap (E.toTorus.pairing.rightCollar j (y', halfZero)) at h'
    rw [E.toTorus.cutMap_rightCollar j (zero_mem_halfCollarSource y),
      E.toTorus.cutMap_rightCollar j (zero_mem_halfCollarSource y')] at h'
    exact (E.toTorus.pairing.matching j).symm.injective
      (congrArg Prod.fst ((E.toTorus.seam j).toPartialEquiv.injOn (hm _) (hm _) h'))

theorem sideCollar_eq_trivialization (i : Fin E.toTorus.components.count)
    (s : E.toTorus.OwnedSide i) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    E.toTorus.sideCollar s.1 p = ((E.piece i).trivialization ((E.piece i).base.collar
      ((E.piece i).port.symm s) (p.1.1, p.2), p.1.2) : E.toTorus.cutCarrier.Carrier) := by
  have h := congrArg Subtype.val ((E.piece i).collar_eq ((E.piece i).port.symm s) p hp)
  rw [Equiv.apply_symm_apply, TorusPresentation.pieceCollar_apply _ i s hp] at h
  exact h

def solidPort (j : Fin E.toTorus.pairing.count) (b : Bool) : Fin (E.kind (E.seamPiece j b)) :=
  (E.piece (E.seamPiece j b)).port.symm ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩

def hostPort (j : Fin E.toTorus.pairing.count) (b : Bool) : Fin (E.kind (E.hostPiece j b)) :=
  (E.piece (E.hostPiece j b)).port.symm ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩

def meridianCircle (j : Fin E.toTorus.pairing.count) (b : Bool) (w : Circle) : Set W.Carrier :=
  range fun z : Circle => E.toTorus.cutMap ((E.piece (E.seamPiece j b)).trivialization
    ((E.piece (E.seamPiece j b)).base.collar (E.solidPort j b) (z, halfZero), w) :
      E.toTorus.cutCarrier.Carrier)

def hostFibre (j : Fin E.toTorus.pairing.count) (b : Bool) (s : Circle) : Set W.Carrier :=
  range fun w : Circle => E.toTorus.cutMap ((E.piece (E.hostPiece j b)).trivialization
    ((E.piece (E.hostPiece j b)).base.collar (E.hostPort j b) (s, halfZero), w) :
      E.toTorus.cutCarrier.Carrier)

theorem meridianCircle_eq (j : Fin E.toTorus.pairing.count) (b : Bool) (w : Circle) :
    E.meridianCircle j b w = range fun z : Circle =>
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) ((z, w), halfZero)) := by
  ext x
  simp only [meridianCircle, mem_range]
  refine exists_congr fun z => ?_
  rw [E.sideCollar_eq_trivialization _ ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩
    (zero_mem_halfCollarSource _)]
  rfl

theorem hostFibre_eq (j : Fin E.toTorus.pairing.count) (b : Bool) (s : Circle) :
    E.hostFibre j b s = range fun w : Circle =>
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j !b) ((s, w), halfZero)) := by
  ext x
  simp only [hostFibre, mem_range]
  refine exists_congr fun w => ?_
  rw [E.sideCollar_eq_trivialization _ ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩
    (zero_mem_halfCollarSource _)]
  rfl

theorem meridianCircle_eq_image (j : Fin E.toTorus.pairing.count) (b : Bool) (w : Circle) :
    E.meridianCircle j b w = (fun y : Torus =>
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j !b) (y, halfZero))) ''
        range fun z : Circle => E.crossMap j b (z, w) := by
  rw [meridianCircle_eq, ← range_comp]
  exact congrArg range (funext fun z => E.cutMap_sideCollar_cross j b (z, w))

theorem hostFibre_eq_image (j : Fin E.toTorus.pairing.count) (b : Bool) (s : Circle) :
    E.hostFibre j b s = (fun y : Torus =>
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j !b) (y, halfZero))) ''
        range fun v : Circle => ((s, v) : Torus) := by
  rw [hostFibre_eq, ← range_comp]
  rfl

variable {E}

theorem IsLinearSeam.meridianCircle_eq_hostFibre {j : Fin E.toTorus.pairing.count}
    (hlin : E.IsLinearSeam j) {b : Bool} (h0 : E.fillingDistance j b = 0) (w : Circle) :
    E.meridianCircle j b w =
      E.hostFibre j b (w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0
  rw [meridianCircle_eq_image, hostFibre_eq_image]
  congr 1
  rw [← range_linearTorusMap_eq_fiber _ h0 (units_entries_of_zero _ h0).1]
  exact congrArg range (funext fun z => hlin.crossMap_apply b (z, w))

theorem IsLinearSeam.exists_meridianCircle_eq_hostFibre {j : Fin E.toTorus.pairing.count}
    (hlin : E.IsLinearSeam j) {b : Bool} (h0 : E.fillingDistance j b = 0) (w : Circle) :
    ∃ s, E.meridianCircle j b w = E.hostFibre j b s :=
  ⟨_, hlin.meridianCircle_eq_hostFibre h0 w⟩

theorem IsLinearSeam.exists_hostFibre_eq_meridianCircle {j : Fin E.toTorus.pairing.count}
    (hlin : E.IsLinearSeam j) {b : Bool} (h0 : E.fillingDistance j b = 0) (s : Circle) :
    ∃ w, E.meridianCircle j b w = E.hostFibre j b s := by
  have h0' := h0
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0'
  refine ⟨s ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, ?_⟩
  rw [hlin.meridianCircle_eq_hostFibre h0, zpow_zpow_of_unit (units_entries_of_zero _ h0').2]

theorem IsLinearSeam.existsUnique_mem_hostFibre {j : Fin E.toTorus.pairing.count}
    (hlin : E.IsLinearSeam j) {b : Bool} (h1 : E.fillingDistance j b = 1) (w s : Circle) :
    ∃! z : Circle, E.toTorus.cutMap ((E.piece (E.seamPiece j b)).trivialization
      ((E.piece (E.seamPiece j b)).base.collar (E.solidPort j b) (z, halfZero), w) :
        E.toTorus.cutCarrier.Carrier) ∈ E.hostFibre j b s := by
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_iff] at h1
  have hB : (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 ∨
      (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1 := by exact_mod_cast h1
  have key : ∀ z : Circle, E.toTorus.cutMap ((E.piece (E.seamPiece j b)).trivialization
      ((E.piece (E.seamPiece j b)).base.collar (E.solidPort j b) (z, halfZero), w) :
        E.toTorus.cutCarrier.Carrier) ∈ E.hostFibre j b s ↔
      (linearTorusMap (E.crossUnit j b) (z, w)).1 = s := by
    intro z
    have e1 : ((E.piece (E.seamPiece j b)).trivialization
        ((E.piece (E.seamPiece j b)).base.collar (E.solidPort j b) (z, halfZero), w) :
          E.toTorus.cutCarrier.Carrier) =
        E.toTorus.sideCollar (E.seamSide j b) ((z, w), halfZero) :=
      (E.sideCollar_eq_trivialization _ ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩
        (zero_mem_halfCollarSource (z, w))).symm
    rw [hostFibre_eq_image, e1, E.cutMap_sideCollar_cross j b,
      (E.cutMap_sideCollar_seamSide_injective j !b).mem_set_image,
      hlin.crossMap_apply b]
    constructor
    · rintro ⟨v, hv⟩
      rw [← hv]
    · intro h
      exact ⟨(linearTorusMap (E.crossUnit j b) (z, w)).2, Prod.ext h.symm rfl⟩
  simp only [key]
  exact existsUnique_linearTorusMap_fst _ hB w s

end ElementaryPresentation

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

def leftOfSide (j : Fin E.toTorus.pairing.count) : Bool → Torus → Torus
  | true => id
  | false => (E.toTorus.pairing.matching j).symm

def sideHeight : Bool → ℝ → ℝ
  | true => fun s => -s
  | false => id

theorem sideHeight_not : ∀ (b : Bool) (s : ℝ), sideHeight (!b) s = -sideHeight b s
  | true, s => by simp [sideHeight]
  | false, s => by simp [sideHeight]

theorem leftOfSide_not_crossMap (j : Fin E.toTorus.pairing.count) :
    ∀ (b : Bool) (t : Torus), E.leftOfSide j (!b) (E.crossMap j b t) = E.leftOfSide j b t
  | true, t => (E.toTorus.pairing.matching j).symm_apply_apply t
  | false, _ => rfl

theorem cutMap_sideCollar_eq_seam (j : Fin E.toTorus.pairing.count) :
    ∀ (b : Bool) (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < 1 →
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (t, halfPoint s hs)) =
        E.toTorus.seam j (E.leftOfSide j b t, sideHeight b s)
  | true, t, s, hs, hs1 => E.toTorus.cutMap_leftCollar j (p := (t, halfPoint s hs)) hs1
  | false, t, s, hs, hs1 => E.toTorus.cutMap_rightCollar j (p := (t, halfPoint s hs)) hs1

variable {E}

theorem IsLinearSeam.seam_junction {j : Fin E.toTorus.pairing.count} (hlin : E.IsLinearSeam j)
    {b : Bool} (h0 : E.fillingDistance j b = 0) (w : Circle) :
    range (fun v : Circle =>
        E.leftOfSide j (!b) ((w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, v))) =
      range (fun z : Circle => E.leftOfSide j b (z, w)) ∧
    (∀ (z : Circle) (s : ℝ) (hs : 0 ≤ s), s < 1 →
      E.toTorus.cutMap ((E.piece (E.seamPiece j b)).trivialization
        ((E.piece (E.seamPiece j b)).base.collar (E.solidPort j b) (z, halfPoint s hs), w) :
          E.toTorus.cutCarrier.Carrier) =
        E.toTorus.seam j (E.leftOfSide j b (z, w), sideHeight b s)) ∧
    ∀ (v : Circle) (s : ℝ) (hs : 0 ≤ s), s < 1 →
      E.toTorus.cutMap ((E.piece (E.hostPiece j b)).trivialization
        ((E.piece (E.hostPiece j b)).base.collar (E.hostPort j b)
          (w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, halfPoint s hs), v) :
            E.toTorus.cutCarrier.Carrier) =
        E.toTorus.seam j (E.leftOfSide j (!b)
          ((w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, v)), -sideHeight b s) := by
  rw [fillingDistance_eq_crossUnit, delta_smul_meridianSlope, Int.natAbs_eq_zero] at h0
  refine ⟨?_, fun z s hs hs1 => ?_, fun v s hs hs1 => ?_⟩
  · have hr := range_linearTorusMap_eq_fiber _ h0 (units_entries_of_zero _ h0).1 w
    calc range (fun v : Circle =>
          E.leftOfSide j (!b) ((w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, v)))
        = E.leftOfSide j (!b) '' range (fun v : Circle =>
          ((w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, v) : Torus)) :=
          range_comp (E.leftOfSide j (!b)) _
      _ = E.leftOfSide j (!b) '' range (fun z : Circle =>
          linearTorusMap (E.crossUnit j b) (z, w)) := by rw [hr]
      _ = range (fun z : Circle =>
          E.leftOfSide j (!b) (linearTorusMap (E.crossUnit j b) (z, w))) :=
          (range_comp (E.leftOfSide j (!b)) _).symm
      _ = range (fun z : Circle => E.leftOfSide j b (z, w)) :=
          congrArg range (funext fun z => by
            rw [← hlin.crossMap_apply b, E.leftOfSide_not_crossMap])
  · have e1 : ((E.piece (E.seamPiece j b)).trivialization
        ((E.piece (E.seamPiece j b)).base.collar (E.solidPort j b) (z, halfPoint s hs), w) :
          E.toTorus.cutCarrier.Carrier) =
        E.toTorus.sideCollar (E.seamSide j b) ((z, w), halfPoint s hs) :=
      (E.sideCollar_eq_trivialization _ ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩
        (p := ((z, w), halfPoint s hs)) hs1).symm
    rw [e1]
    exact E.cutMap_sideCollar_eq_seam j b (z, w) s hs hs1
  · have e1 : ((E.piece (E.hostPiece j b)).trivialization
        ((E.piece (E.hostPiece j b)).base.collar (E.hostPort j b)
          (w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, halfPoint s hs), v) :
            E.toTorus.cutCarrier.Carrier) =
        E.toTorus.sideCollar (E.seamSide j !b)
          ((w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, v), halfPoint s hs) :=
      (E.sideCollar_eq_trivialization _ ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩
        (p := ((w ^ (E.crossUnit j b : Matrix (Fin 2) (Fin 2) ℤ) 0 1, v), halfPoint s hs))
        hs1).symm
    rw [e1, ← sideHeight_not]
    exact E.cutMap_sideCollar_eq_seam j (!b) _ s hs hs1

end ElementaryPresentation

end GC.Seifert
