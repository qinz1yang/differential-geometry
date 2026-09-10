import DifferentialGeometry.Topology.VectorField.FiniteZeros
import DifferentialGeometry.Topology.VectorField.CollarExtension
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.VectorField


def collarNormalizationTime (ε s : ℝ) : ℝ :=
  (1 - collarTransition (1 + s / ε)) * s


def collarNormalizationTimeHomotopy (ε u s : ℝ) : ℝ :=
  (1 - u) * s + u * collarNormalizationTime ε s


theorem contDiff_collarNormalizationTime (ε : ℝ) :
    ContDiff ℝ ∞ (collarNormalizationTime ε) :=
  (contDiff_const.sub (contDiff_collarTransition.comp
    (contDiff_const.add (contDiff_id.div_const ε)))).mul contDiff_id


theorem contDiff_collarNormalizationTimeHomotopy (ε : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => collarNormalizationTimeHomotopy ε p.1 p.2) :=
  ((contDiff_const.sub contDiff_fst).mul contDiff_snd).add
    (contDiff_fst.mul ((contDiff_collarNormalizationTime ε).comp contDiff_snd))


theorem collarNormalizationTime_eq_self {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ -(2 * ε / 3)) :
    collarNormalizationTime ε s = s := by
  have harg : 1 + s / ε ≤ 1 / 3 := by
    have hd : s / ε ≤ -(2 / 3 : ℝ) := (div_le_iff₀ hε).mpr (by linarith)
    linarith
  rw [collarNormalizationTime, collarTransition_eq_zero harg]
  ring


theorem collarNormalizationTime_eq_zero {ε s : ℝ} (hε : 0 < ε) (hs : -ε / 3 ≤ s) :
    collarNormalizationTime ε s = 0 := by
  have harg : 2 / 3 ≤ 1 + s / ε := by
    have hd : -(1 / 3 : ℝ) ≤ s / ε := (le_div_iff₀ hε).mpr (by linarith)
    linarith
  rw [collarNormalizationTime, collarTransition_eq_one harg]
  ring

@[simp]
theorem collarNormalizationTime_zero (ε : ℝ) : collarNormalizationTime ε 0 = 0 := by
  simp [collarNormalizationTime]

@[simp]
theorem collarNormalizationTimeHomotopy_zero (ε s : ℝ) :
    collarNormalizationTimeHomotopy ε 0 s = s := by simp [collarNormalizationTimeHomotopy]

@[simp]
theorem collarNormalizationTimeHomotopy_one (ε s : ℝ) :
    collarNormalizationTimeHomotopy ε 1 s = collarNormalizationTime ε s := by
  simp [collarNormalizationTimeHomotopy]

@[simp]
theorem collarNormalizationTimeHomotopy_boundary (ε u : ℝ) :
    collarNormalizationTimeHomotopy ε u 0 = 0 := by
  simp [collarNormalizationTimeHomotopy]


theorem collarNormalizationTimeHomotopy_mem_Icc {ε u s : ℝ}
    (hu : u ∈ Icc 0 1) (hs : s ∈ Icc (-ε) 0) :
    collarNormalizationTimeHomotopy ε u s ∈ Icc (-ε) 0 := by
  obtain ⟨hρ0, hρ1⟩ := collarTransition_mem_Icc (1 + s / ε)
  have hφlo : s ≤ collarNormalizationTime ε s := by
    dsimp [collarNormalizationTime]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ0 hs.2]
  have hφhi : collarNormalizationTime ε s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hs.2
  dsimp [collarNormalizationTimeHomotopy]
  constructor <;> nlinarith [hs.1, mul_nonneg hu.1 (sub_nonneg.mpr hφlo),
    mul_nonpos_of_nonneg_of_nonpos hu.1 hφhi,
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu.2) hs.2]


theorem collarNormalizationTimeHomotopy_eq_self {ε s : ℝ} (u : ℝ)
    (hε : 0 < ε) (hs : s ≤ -(2 * ε / 3)) :
    collarNormalizationTimeHomotopy ε u s = s := by
  rw [collarNormalizationTimeHomotopy, collarNormalizationTime_eq_self hε hs]
  ring

section ProductManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def collarReparametrization
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (φ : ℝ → ℝ)
    (p : M × ℝ) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p :=
  ((V (p.1, φ p.2)).1, (V (p.1, φ p.2)).2)

theorem equivTangentBundleProd_collarReparametrization
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (φ : ℝ → ℝ) (p : M × ℝ) :
    equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ ⟨p, collarReparametrization V φ p⟩ =
      (⟨p.1, (V (p.1, φ p.2)).1⟩, ⟨p.2, (V (p.1, φ p.2)).2⟩) := rfl


def collarNormalization
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε u : ℝ) :=
  collarReparametrization V (collarNormalizationTimeHomotopy ε u)

theorem contMDiff_collarReparametrization [IsManifold I 1 M] {n : ℕ∞ω}
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {φ : ℝ → ℝ}
    (hV : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent n
      (fun p => (⟨p, V p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (hφ : ContDiff ℝ n φ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent n
      (fun p => (⟨p, collarReparametrization V φ p⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hbase : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) n
      (fun p : M × ℝ => (p.1, φ p.2)) :=
    contMDiff_fst.prodMk (hφ.contMDiff.comp contMDiff_snd)
  have hcomp := contMDiff_equivTangentBundleProd.comp (hV.comp hbase)
  have hN := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hcomp.snd
  have hR : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent n
      (fun p : M × ℝ => (⟨p.2, (V (p.1, φ p.2)).2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro p
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiff_snd p, ?_⟩
    convert hN p using 1
    simp only [mfld_simps]
    rfl
  exact contMDiff_equivTangentBundleProd_symm.comp (hcomp.fst.prodMk hR)


theorem contMDiff_collarNormalization [IsManifold I 1 M]
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    (hV : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, V p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))) (ε u : ℝ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, collarNormalization V ε u p⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) :=
  contMDiff_collarReparametrization hV
    ((contDiff_collarNormalizationTimeHomotopy ε).comp (contDiff_const.prodMk contDiff_id))


theorem contMDiff_collarNormalization_joint [IsManifold I 1 M]
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    (hV : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p => (⟨p, V p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))) (ε : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun q : ℝ × (M × ℝ) => (⟨q.2, collarNormalization V ε q.1 q.2⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have htime : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × (M × ℝ) => collarNormalizationTimeHomotopy ε q.1 q.2.2) :=
    ((contMDiff_const.sub contMDiff_fst).mul
      (contMDiff_snd.comp contMDiff_snd)).add (contMDiff_fst.mul
        ((contDiff_collarNormalizationTime ε).contMDiff.comp
          (contMDiff_snd.comp contMDiff_snd)))
  have hbase : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × (M × ℝ) => (q.2.1, collarNormalizationTimeHomotopy ε q.1 q.2.2)) :=
    (contMDiff_fst.comp contMDiff_snd).prodMk htime
  have hcomp := contMDiff_equivTangentBundleProd.comp (hV.comp hbase)
  have hN := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hcomp.snd
  have hR : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, ℝ).tangent ∞
      (fun q : ℝ × (M × ℝ) => (⟨q.2.2,
        (V (q.2.1, collarNormalizationTimeHomotopy ε q.1 q.2.2)).2⟩ :
          TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro q
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨(contMDiff_snd.comp contMDiff_snd) q, ?_⟩
    convert hN q using 1
    simp only [mfld_simps]
    rfl
  exact contMDiff_equivTangentBundleProd_symm.comp (hcomp.fst.prodMk hR)

theorem exists_pos_ne_zero_on_product_strip [IsManifold I 1 M] [CompactSpace M]
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    (hV : Continuous (fun p => (⟨p, V p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (hzero : ∀ x, V (x, 0) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x t, t ∈ Icc (-ε) ε → V (x, t) ≠ 0 := by
  have hopen : IsOpen {p : M × ℝ | V p ≠ 0} :=
    (DifferentialGeometry.VectorBundle.isClosed_zeroSet ℝ hV).isOpen_compl
  have hslice : (univ : Set M) ×ˢ ({0} : Set ℝ) ⊆ {p | V p ≠ 0} := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have : t = 0 := ht
    subst t
    exact hzero x
  obtain ⟨U, J, _, hJ, hU, hJ0, hprod⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hopen hslice
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds (hJ0 (show (0 : ℝ) ∈ {0} from rfl)))
  refine ⟨δ / 2, half_pos hδ, fun x t ht => hprod ⟨hU (mem_univ x), hball ?_⟩⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩


@[simp]
theorem collarNormalization_zero
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε : ℝ) (p : M × ℝ) :
    collarNormalization V ε 0 p = V p := by
  change (V (p.1, collarNormalizationTimeHomotopy ε 0 p.2) : E × ℝ) = V p
  exact congrArg (fun q : M × ℝ => (V q : E × ℝ))
    (Prod.ext rfl (collarNormalizationTimeHomotopy_zero ε p.2))


theorem collarNormalization_eq_self
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) {ε : ℝ} (u : ℝ)
    (hε : 0 < ε) {p : M × ℝ} (hp : p.2 ≤ -(2 * ε / 3)) :
    collarNormalization V ε u p = V p := by
  change (V (p.1, collarNormalizationTimeHomotopy ε u p.2) : E × ℝ) = V p
  exact congrArg (fun q : M × ℝ => (V q : E × ℝ))
    (Prod.ext rfl (collarNormalizationTimeHomotopy_eq_self u hε hp))


theorem collarNormalization_boundary
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (ε u : ℝ) (x : M) :
    collarNormalization V ε u (x, 0) = V (x, 0) := by
  change (V (x, collarNormalizationTimeHomotopy ε u 0) : E × ℝ) = V (x, 0)
  exact congrArg (fun q : M × ℝ => (V q : E × ℝ))
    (Prod.ext rfl (collarNormalizationTimeHomotopy_boundary ε u))

theorem collarNormalization_one_eq_boundary
    (V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) {ε : ℝ}
    (hε : 0 < ε) {p : M × ℝ} (hp : -ε / 3 ≤ p.2) :
    collarNormalization V ε 1 p = ((V (p.1, 0)).1, (V (p.1, 0)).2) := by
  change (V (p.1, collarNormalizationTimeHomotopy ε 1 p.2) : E × ℝ) = V (p.1, 0)
  exact congrArg (fun q : M × ℝ => (V q : E × ℝ))
    (Prod.ext rfl ((collarNormalizationTimeHomotopy_one ε p.2).trans
      (collarNormalizationTime_eq_zero hε hp)))


theorem collarNormalization_ne_zero
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {ε u : ℝ}
    (hstrip : ∀ x t, t ∈ Icc (-ε) 0 → V (x, t) ≠ 0)
    (hu : u ∈ Icc 0 1) {p : M × ℝ} (hp : p.2 ∈ Icc (-ε) 0) :
    collarNormalization V ε u p ≠ 0 := by
  exact hstrip p.1 _ (collarNormalizationTimeHomotopy_mem_Icc hu hp)

theorem collarNormalization_eq_zero_iff
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {ε u : ℝ}
    (hε : 0 < ε) (hstrip : ∀ x t, t ∈ Icc (-ε) 0 → V (x, t) ≠ 0)
    (hu : u ∈ Icc 0 1) {p : M × ℝ} (hp : p.2 ≤ 0) :
    collarNormalization V ε u p = 0 ↔ V p = 0 := by
  by_cases ht : p.2 ≤ -(2 * ε / 3)
  · rw [collarNormalization_eq_self V u hε ht]
  · have hmem : p.2 ∈ Icc (-ε) 0 := ⟨by linarith, hp⟩
    exact iff_of_false (collarNormalization_ne_zero hstrip hu hmem) (hstrip p.1 p.2 hmem)

theorem collarNormalization_eventuallyEq_of_zero
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p} {ε : ℝ} (u : ℝ)
    (hε : 0 < ε) (hstrip : ∀ x t, t ∈ Icc (-ε) 0 → V (x, t) ≠ 0)
    {p : M × ℝ} (hp : V p = 0) (hp0 : p.2 ≤ 0) :
    (fun q => (⟨q, collarNormalization V ε u q⟩ :
      TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) =ᶠ[𝓝 p]
      (fun q => (⟨q, V q⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hpt : p.2 < -ε := lt_of_not_ge (fun h => hstrip p.1 p.2 ⟨h, hp0⟩ hp)
  have hopen : IsOpen {q : M × ℝ | q.2 < -(2 * ε / 3)} :=
    isOpen_lt continuous_snd continuous_const
  have hnear : ∀ᶠ q : M × ℝ in 𝓝 p, q.2 < -(2 * ε / 3) :=
    hopen.mem_nhds (show p.2 < -(2 * ε / 3) by linarith)
  filter_upwards [hnear] with q hq
  exact congrArg (fun z : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q =>
    (⟨q, z⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))
    (collarNormalization_eq_self V u hε hq.le)

theorem exists_pos_collarNormalization_ne_zero [IsManifold I 1 M] [CompactSpace M]
    {V : ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p}
    (hV : Continuous (fun p => (⟨p, V p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (hzero : ∀ x, V (x, 0) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ Icc (0 : ℝ) 1, ∀ x s, s ∈ Icc (-ε) 0 →
      collarNormalization V ε u (x, s) ≠ 0 := by
  obtain ⟨ε, hε, hstrip⟩ := exists_pos_ne_zero_on_product_strip hV hzero
  refine ⟨ε, hε, fun u hu x s hs => collarNormalization_ne_zero ?_ hu hs⟩
  intro y t ht
  exact hstrip y t ⟨ht.1, ht.2.trans hε.le⟩

end ProductManifold

end DifferentialGeometry.VectorField
