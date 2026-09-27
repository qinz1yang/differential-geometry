import DifferentialGeometry.Topology.Morse.Attachment.ManifoldHandle
import DifferentialGeometry.Topology.Handle.Embedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

open CellAttachment
open DifferentialGeometry.Topology.Handle

noncomputable section

private def cocoreCoordinates {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (y : MorseModel n) : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) :=
  ((Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y,
    r⁻¹ • posPart hk y)

private def cocoreParametrization {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) : MorseModel n :=
  recombine hk (Real.sqrt (2 * ε + r ^ 2 * ‖v‖ ^ 2) • u) (r • v)

private theorem cocoreCoordinates_parametrization {n k : ℕ} (hk : k ≤ n)
    (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) :
    cocoreCoordinates hk ε r (cocoreParametrization hk ε r u v) = (u, v) := by
  have hs : ‖r • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpos : 0 < Real.sqrt (2 * ε + r ^ 2 * ‖v‖ ^ 2) := by positivity
  simp only [cocoreCoordinates, cocoreParametrization, posPart_recombine, negPart_recombine,
    hs, smul_smul, inv_mul_cancel₀ hpos.ne', inv_mul_cancel₀ hr, one_smul]

private theorem morseNormalForm_cocoreParametrization {n k : ℕ} (hk : k ≤ n)
    (c ε r : ℝ) (hε : 0 < ε) (u : CellBoundary k)
    (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (cocoreParametrization hk ε r u.val v) = c - ε := by
  have hs : ‖r • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hn : ‖Real.sqrt (2 * ε + r ^ 2 * ‖v‖ ^ 2) • u.val‖ ^ 2 =
      2 * ε + r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, u.property, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  rw [cocoreParametrization, morseNormalForm_split, posPart_recombine,
    negPart_recombine, hn, hs]
  ring

private theorem cocoreCoordinates_cocoreModelPoint {n k : ℕ} (hk : k ≤ n)
    (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0)
    (p : AttachingRegion k (n - k)) :
    cocoreCoordinates hk ε r (cocoreModelPoint hk ε r p) = (p.1.val, p.2.val) := by
  have hs : ‖r • p.2.val‖ ^ 2 = r ^ 2 * ‖p.2.val‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpos : 0 < Real.sqrt (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) := by positivity
  simp only [cocoreCoordinates, cocoreModelPoint, posPart_recombine, negPart_recombine,
    negPart_cellMap_smul, hs, smul_smul, inv_mul_cancel₀ hpos.ne', inv_mul_cancel₀ hr,
    one_smul]

private theorem cocoreCoordinates_norm_fst {n k : ℕ} (hk : k ≤ n)
    (c ε r : ℝ) (hε : 0 < ε) {y : MorseModel n}
    (hy : morseNormalForm hk c y = c - ε) :
    ‖(cocoreCoordinates hk ε r y).1‖ = 1 := by
  have hsq : ‖negPart hk y‖ ^ 2 = 2 * ε + ‖posPart hk y‖ ^ 2 := by
    rw [morseNormalForm_split] at hy
    linarith
  have hsqrt : Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2) = ‖negPart hk y‖ := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hn : ‖negPart hk y‖ ≠ 0 := by
    have hpos : 0 < ‖negPart hk y‖ ^ 2 := by rw [hsq]; positivity
    exact (pow_ne_zero_iff (by norm_num : 2 ≠ 0)).mp hpos.ne'
  dsimp [cocoreCoordinates]
  rw [hsqrt, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ hn]

private theorem cocoreCoordinates_recombine {n k : ℕ} (hk : k ≤ n)
    (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0) (y : MorseModel n) :
    recombine hk
      (Real.sqrt (2 * ε + r ^ 2 * ‖(cocoreCoordinates hk ε r y).2‖ ^ 2) •
        (cocoreCoordinates hk ε r y).1)
      (r • (cocoreCoordinates hk ε r y).2) = y := by
  have hs : r ^ 2 * ‖r⁻¹ • posPart hk y‖ ^ 2 = ‖posPart hk y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]
  have hpos : 0 < Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2) := by positivity
  dsimp [cocoreCoordinates]
  rw [hs, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, smul_smul,
    mul_inv_cancel₀ hr, one_smul, recombine_decompose]

private theorem contDiff_cocoreCoordinates {n k : ℕ} (hk : k ≤ n)
    (ε r : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (cocoreCoordinates hk ε r) := by
  have hneg : ContDiff ℝ ∞ (negPart hk) := by
    apply (contDiff_piLp 2).2
    intro i
    change ContDiff ℝ ∞ (fun y : MorseModel n => y (negIdx hk i))
    fun_prop
  have hpos : ContDiff ℝ ∞ (posPart hk) := by
    apply (contDiff_piLp 2).2
    intro i
    change ContDiff ℝ ∞ (fun y : MorseModel n => y (posIdx hk i))
    fun_prop
  have hsqrt : ContDiff ℝ ∞
      (fun y : MorseModel n => Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2)) := by
    apply ContDiff.sqrt
    · exact contDiff_const.add ((contDiff_norm_sq ℝ).comp hpos)
    · intro y
      positivity
  exact (hsqrt.inv (fun y => by positivity) |>.smul hneg).prodMk
    ((contDiff_const (c := r⁻¹)).smul hpos)

private def cellBoundaryChartValue (k : ℕ) [NeZero k] (u : CellBoundary k) :
    EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin (k - 1)) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (k - 1)
    (ne_zero_of_mem_unit_sphere (cellBoundarySphereHomeomorph k u))).repr ∘
    stereoToFun u.val

private theorem cellBoundaryChartValue_apply (k : ℕ) [NeZero k]
    (u v : CellBoundary k) :
    cellBoundaryChartValue k u v.val = cellBoundaryChart k u v := rfl

private theorem contDiffOn_cellBoundaryChartValue (k : ℕ) [NeZero k]
    (u : CellBoundary k) :
    ContDiffOn ℝ ∞ (cellBoundaryChartValue k u)
      {v : EuclideanSpace ℝ (Fin k) | inner ℝ u.val v ≠ 1} := by
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (k - 1)
    (ne_zero_of_mem_unit_sphere (cellBoundarySphereHomeomorph k u))).repr.contDiff.comp_contDiffOn
    contDiffOn_stereoToFun

private theorem cellBoundaryChart_target (k : ℕ) [NeZero k] (u : CellBoundary k) :
    (cellBoundaryChart k u).target = Set.univ := by
  simp [cellBoundaryChart]

private theorem cellBoundaryChart_source_iff (k : ℕ) [NeZero k]
    (u v : CellBoundary k) :
    v ∈ (cellBoundaryChart k u).source ↔ inner ℝ u.val v.val ≠ 1 := by
  have hu : ‖u.val‖ = 1 := u.property
  have hv : ‖v.val‖ = 1 := v.property
  simp only [cellBoundaryChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.univ_inter, Set.mem_preimage,
    stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff]
  have hval : cellBoundarySphereHomeomorph k v = cellBoundarySphereHomeomorph k u ↔
      u.val = v.val := by
    constructor
    · intro h
      exact (congrArg Subtype.val h).symm
    · intro h
      exact Subtype.ext h.symm
  change ¬cellBoundarySphereHomeomorph k v = cellBoundarySphereHomeomorph k u ↔ _
  rw [hval]
  exact (not_congr (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) hu hv)).symm

private theorem contDiff_cellBoundaryChart_symm_val (k : ℕ) [NeZero k]
    (u : CellBoundary k) :
    ContDiff ℝ ∞ (fun z => ((cellBoundaryChart k u).symm z).val) := by
  let _ := cellBoundaryChartedSpace k
  let _ := cellBoundaryIsManifold k
  have hs : cellBoundaryChart k u ∈ IsManifold.maximalAtlas (𝓡 (k - 1)) ∞
      (CellBoundary k) := IsManifold.subset_maximalAtlas ⟨u, rfl⟩
  have h := (cellBoundaryInclusion_contMDiff k).comp_contMDiffOn
    (contMDiffOn_symm_of_mem_maximalAtlas hs)
  rw [cellBoundaryChart_target, contMDiffOn_univ] at h
  exact h.contDiff

private theorem contMDiffOn_levelSet_of_val {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HX : Type} [TopologicalSpace HX] {IX : ModelWithCorners ℝ E HX}
    {X : Type} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
    (G : X → LevelSetSpace f a) (s : Set X) (hs : IsOpen s)
    (hG : ContMDiffOn IX I ∞ (fun x => (G x).val) s) :
    letI := manifoldLevelSetChartedSpace I f a hf hreg
    ContMDiffOn IX 𝓘(ℝ, MorseModel m) ∞ G s := by
  let _ := manifoldLevelSetChartedSpace I f a hf hreg
  let U : TopologicalSpace.Opens X := ⟨s, hs⟩
  have hv : ContMDiff IX I ∞ (fun x : U => (G x.val).val) := by
    intro x
    exact contMDiffAt_subtype_iff.mpr
      ((hG x.val x.property).contMDiffAt (hs.mem_nhds x.property))
  have h : ContMDiff IX 𝓘(ℝ, MorseModel m) ∞ (fun x : U => G x.val) :=
    contMDiff_levelSet_factor I f a hf hreg
      (fun x : U => (G x.val).val) hv (fun x => (G x.val).property)
  change ContMDiffOn IX 𝓘(ℝ, MorseModel m) ∞ G s
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contMDiffWithinAt

private theorem contDiff_cocoreParametrization {n k : ℕ} (hk : k ≤ n)
    (ε r : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
      cocoreParametrization hk ε r z.1 z.2) := by
  simpa only [cocoreParametrization, negPart_cellMap_smul] using
    recombine_contDiff_cocore hk r ε hε

private theorem continuous_cocoreModelPoint {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) :
    Continuous (cocoreModelPoint hk ε r) := by
  have hu : Continuous (fun p : AttachingRegion k (n - k) => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun p : AttachingRegion k (n - k) => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hs : Continuous (fun p : AttachingRegion k (n - k) =>
      Real.sqrt (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2)) :=
    Real.continuous_sqrt.comp
      ((continuous_const (y := 2 * ε)).add ((continuous_const (y := r ^ 2)).mul (hv.norm.pow 2)))
  have hp : Continuous (fun p : AttachingRegion k (n - k) =>
      (Real.sqrt (2 * ε + r ^ 2 * ‖p.2.val‖ ^ 2) • p.1.val, r • p.2.val)) :=
    (hs.smul hu).prodMk ((continuous_const (y := r)).smul hv)
  unfold cocoreModelPoint
  simp only [negPart_cellMap_smul]
  exact (continuous_recombine hk).comp hp

private theorem isEmbedding_cocoreModelPoint {n k : ℕ} (hk : k ≤ n)
    (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0) :
    Topology.IsEmbedding (cocoreModelPoint hk ε r) := by
  apply Topology.IsEmbedding.of_comp (continuous_cocoreModelPoint hk ε r)
    (contDiff_cocoreCoordinates hk ε r hε).continuous
  have heq : cocoreCoordinates hk ε r ∘ cocoreModelPoint hk ε r =
      fun p : AttachingRegion k (n - k) => (p.1.val, p.2.val) :=
    funext (cocoreCoordinates_cocoreModelPoint hk ε r hε hr)
  rw [heq]
  exact Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.subtypeVal

theorem isEmbedding_cocoreAttachingEmbedding {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f) (hε : 0 < ε) (hr : r ≠ 0)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    Topology.IsEmbedding (cocoreAttachingEmbedding hk c ε r data hε hεr) := by
  let g : AttachingRegion k (n - k) → data.χ.source := fun p =>
    ⟨cocoreModelPoint hk ε r p,
      data.closedBall_subset_source _ ((cocoreModelPoint_norm_le hk ε r hε.le p).trans hεr)⟩
  have hg : Topology.IsEmbedding g := Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    (isEmbedding_cocoreModelPoint hk ε r hε hr)
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact data.χ.isEmbedding_restrict.comp hg

section LevelChart

variable {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
  (data : MorseChart (m + 1) k hk c I f) [NeZero k]
  (pole : CellBoundary k)
  (b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1 - k)))
    (EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))))

local notation "Q" => EuclideanSpace ℝ (Fin (k - 1)) ×
  EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))

private def cocoreLevelChartModelSet : Set (MorseModel (m + 1)) :=
  {y | morseNorm (m + 1) y < data.R ∧ ‖y‖ < data.smoothRadius ∧
    inner ℝ pole.val (cocoreCoordinates hk ε r y).1 ≠ 1 ∧
    (cocoreCoordinates hk ε r y).2 ∈ b.source}

private def cocoreLevelChartSource : Set (LevelSetSpace f (c - ε)) :=
  Subtype.val ⁻¹' (data.χ.target ∩ data.χ.symm ⁻¹'
    cocoreLevelChartModelSet hk c ε r data pole b)

private def cocoreLevelChartForward (x : LevelSetSpace f (c - ε)) : Q :=
  (cellBoundaryChartValue k pole (cocoreCoordinates hk ε r (data.χ.symm x.val)).1,
    b (cocoreCoordinates hk ε r (data.χ.symm x.val)).2)

private def cocoreLevelChartInvPoint (z : Q) : MorseModel (m + 1) :=
  cocoreParametrization hk ε r ((cellBoundaryChart k pole).symm z.1).val (b.symm z.2)

private def cocoreLevelChartTarget : Set Q :=
  {z | z.2 ∈ b.target ∧
    morseNorm (m + 1) (cocoreLevelChartInvPoint hk ε r pole b z) < data.R ∧
    ‖cocoreLevelChartInvPoint hk ε r pole b z‖ < data.smoothRadius}

omit [NeZero k] in
private theorem isOpen_cocoreLevelChartSource (hε : 0 < ε) :
    IsOpen (cocoreLevelChartSource hk c ε r data pole b) := by
  have hnorm : Continuous (morseNorm (m + 1)) := by
    exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin (m + 1) => ℝ))
  have hc := (contDiff_cocoreCoordinates hk ε r hε).continuous
  have hu : IsOpen (cocoreLevelChartModelSet hk c ε r data pole b) :=
    (isOpen_lt hnorm continuous_const).inter
      ((isOpen_lt continuous_norm continuous_const).inter
        ((isOpen_ne_fun (continuous_const.inner hc.fst) continuous_const).inter
          (b.open_source.preimage hc.snd)))
  exact (data.χ.isOpen_inter_preimage_symm hu).preimage continuous_subtype_val

private theorem contDiffOn_cocoreLevelChartInvPoint (hε : 0 < ε)
    (hb : ContDiffOn ℝ ∞ b.symm b.target) :
    ContDiffOn ℝ ∞ (cocoreLevelChartInvPoint hk ε r pole b)
      {z : Q | z.2 ∈ b.target} := by
  have hu : ContDiff ℝ ∞ (fun z : Q => ((cellBoundaryChart k pole).symm z.1).val) :=
    (contDiff_cellBoundaryChart_symm_val k pole).comp contDiff_fst
  have hv : ContDiffOn ℝ ∞ (fun z : Q => b.symm z.2) {z : Q | z.2 ∈ b.target} :=
    hb.comp contDiff_snd.contDiffOn (fun z hz => hz)
  have huv : ContDiffOn ℝ ∞
      (fun z : Q => (((cellBoundaryChart k pole).symm z.1).val, b.symm z.2))
      {z : Q | z.2 ∈ b.target} := hu.contDiffOn.prodMk hv
  change ContDiffOn ℝ ∞
    ((fun z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (m + 1 - k)) =>
      cocoreParametrization hk ε r z.1 z.2) ∘
      fun z : Q => (((cellBoundaryChart k pole).symm z.1).val, b.symm z.2)) _
  exact (contDiff_cocoreParametrization hk ε r hε).comp_contDiffOn huv

private theorem isOpen_cocoreLevelChartTarget (hε : 0 < ε)
    (hb : ContDiffOn ℝ ∞ b.symm b.target) :
    IsOpen (cocoreLevelChartTarget hk c ε r data pole b) := by
  have hnorm : Continuous (morseNorm (m + 1)) := by
    exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin (m + 1) => ℝ))
  exact (contDiffOn_cocoreLevelChartInvPoint hk ε r pole b hε hb).continuousOn.isOpen_inter_preimage
    (b.open_target.preimage continuous_snd)
    ((isOpen_lt hnorm continuous_const).inter (isOpen_lt continuous_norm continuous_const))

private theorem cocoreLevelChart_forward_inverse (hε : 0 < ε) (hr : r ≠ 0)
    (x : LevelSetSpace f (c - ε))
    (hx : x ∈ cocoreLevelChartSource hk c ε r data pole b) :
    cocoreLevelChartInvPoint hk ε r pole b
      (cocoreLevelChartForward hk c ε r data pole b x) = data.χ.symm x.val := by
  have hn : morseNormalForm hk c (data.χ.symm x.val) = c - ε := by
    rw [← data.normalForm_on _ hx.2.1.le, data.χ.right_inv hx.1]
    exact x.property
  let u : CellBoundary k :=
    ⟨(cocoreCoordinates hk ε r (data.χ.symm x.val)).1,
      cocoreCoordinates_norm_fst hk c ε r hε hn⟩
  have hu : u ∈ (cellBoundaryChart k pole).source :=
    (cellBoundaryChart_source_iff k pole u).mpr hx.2.2.2.1
  change cocoreParametrization hk ε r
    ((cellBoundaryChart k pole).symm (cellBoundaryChartValue k pole u.val)).val
    (b.symm (b (cocoreCoordinates hk ε r (data.χ.symm x.val)).2)) = _
  rw [cellBoundaryChartValue_apply, (cellBoundaryChart k pole).left_inv hu,
    b.left_inv hx.2.2.2.2]
  exact cocoreCoordinates_recombine hk ε r hε hr (data.χ.symm x.val)

private theorem cocoreLevelChart_map_source (hε : 0 < ε) (hr : r ≠ 0)
    (x : LevelSetSpace f (c - ε))
    (hx : x ∈ cocoreLevelChartSource hk c ε r data pole b) :
    cocoreLevelChartForward hk c ε r data pole b x ∈
      cocoreLevelChartTarget hk c ε r data pole b := by
  exact ⟨b.map_source hx.2.2.2.2,
    (cocoreLevelChart_forward_inverse hk c ε r data pole b hε hr x hx).symm ▸ hx.2.1,
    (cocoreLevelChart_forward_inverse hk c ε r data pole b hε hr x hx).symm ▸ hx.2.2.1⟩

private theorem cocoreLevelChart_invPoint_value (hε : 0 < ε) (z : Q)
    (hz : z ∈ cocoreLevelChartTarget hk c ε r data pole b) :
    f (data.χ (cocoreLevelChartInvPoint hk ε r pole b z)) = c - ε := by
  rw [data.normalForm_on _ hz.2.1.le]
  exact morseNormalForm_cocoreParametrization hk c ε r hε _ _

private theorem cocoreLevelChartForward_cocore (hε : 0 < ε) (hr : r ≠ 0)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (p : AttachingRegion k (m + 1 - k)) :
    cocoreLevelChartForward hk c ε r data pole b
      (cocoreAttachingEmbedding hk c ε r data hε hεr p) =
      (cellBoundaryChart k pole p.1, b p.2.val) := by
  have hsrc : cocoreModelPoint hk ε r p ∈ data.χ.source :=
    data.closedBall_subset_source _ ((cocoreModelPoint_norm_le hk ε r hε.le p).trans hεr)
  change (cellBoundaryChartValue k pole
      (cocoreCoordinates hk ε r (data.χ.symm (data.χ (cocoreModelPoint hk ε r p)))).1,
    b (cocoreCoordinates hk ε r (data.χ.symm (data.χ (cocoreModelPoint hk ε r p)))).2) = _
  rw [data.χ.left_inv hsrc, cocoreCoordinates_cocoreModelPoint hk ε r hε hr p,
    cellBoundaryChartValue_apply]

private theorem cocore_mem_cocoreLevelChartSource (hε : 0 < ε) (hr : r ≠ 0)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.smoothRadius)
    (p : AttachingRegion k (m + 1 - k))
    (hp₁ : p.1 ∈ (cellBoundaryChart k pole).source) (hp₂ : p.2.val ∈ b.source) :
    cocoreAttachingEmbedding hk c ε r data hε hεr.le p ∈
      cocoreLevelChartSource hk c ε r data pole b := by
  have hR := (cocoreModelPoint_norm_le hk ε r hε.le p).trans_lt hεr
  have hR' := (morseNorm_piNorm_le (cocoreModelPoint hk ε r p)).trans_lt
    ((cocoreModelPoint_norm_le hk ε r hε.le p).trans_lt hεr')
  have hsrc := data.closedBall_subset_source _ hR.le
  refine ⟨data.χ.map_source hsrc, ?_⟩
  change data.χ.symm (data.χ (cocoreModelPoint hk ε r p)) ∈
    cocoreLevelChartModelSet hk c ε r data pole b
  rw [data.χ.left_inv hsrc]
  change morseNorm (m + 1) (cocoreModelPoint hk ε r p) < data.R ∧ _
  refine ⟨hR, hR', ?_, ?_⟩
  · rw [cocoreCoordinates_cocoreModelPoint hk ε r hε hr p]
    exact (cellBoundaryChart_source_iff k pole p.1).mp hp₁
  · rw [cocoreCoordinates_cocoreModelPoint hk ε r hε hr p]
    exact hp₂

private def cocoreLevelChartInverse (x₀ : LevelSetSpace f (c - ε))
    (z : Q) : LevelSetSpace f (c - ε) :=
  if hz : f (data.χ (cocoreLevelChartInvPoint hk ε r pole b z)) = c - ε then
    ⟨data.χ (cocoreLevelChartInvPoint hk ε r pole b z), hz⟩
  else x₀

private theorem cocoreLevelChartInverse_val (hε : 0 < ε)
    (x₀ : LevelSetSpace f (c - ε)) (z : Q)
    (hz : z ∈ cocoreLevelChartTarget hk c ε r data pole b) :
    (cocoreLevelChartInverse hk c ε r data pole b x₀ z).val =
      data.χ (cocoreLevelChartInvPoint hk ε r pole b z) := by
  simp only [cocoreLevelChartInverse,
    dif_pos (cocoreLevelChart_invPoint_value hk c ε r data pole b hε z hz)]

private theorem cocoreLevelChart_inverse_coordinates (hε : 0 < ε) (hr : r ≠ 0)
    (x₀ : LevelSetSpace f (c - ε)) (z : Q)
    (hz : z ∈ cocoreLevelChartTarget hk c ε r data pole b) :
    cocoreCoordinates hk ε r
      (data.χ.symm (cocoreLevelChartInverse hk c ε r data pole b x₀ z).val) =
      (((cellBoundaryChart k pole).symm z.1).val, b.symm z.2) := by
  rw [cocoreLevelChartInverse_val hk c ε r data pole b hε x₀ z hz,
    data.χ.left_inv (data.closedBall_subset_source _ hz.2.1.le)]
  exact cocoreCoordinates_parametrization hk ε r hε hr _ _

private theorem cocoreLevelChart_map_target (hε : 0 < ε) (hr : r ≠ 0)
    (x₀ : LevelSetSpace f (c - ε)) (z : Q)
    (hz : z ∈ cocoreLevelChartTarget hk c ε r data pole b) :
    cocoreLevelChartInverse hk c ε r data pole b x₀ z ∈
      cocoreLevelChartSource hk c ε r data pole b := by
  have hχ : data.χ.symm (cocoreLevelChartInverse hk c ε r data pole b x₀ z).val =
      cocoreLevelChartInvPoint hk ε r pole b z := by
    rw [cocoreLevelChartInverse_val hk c ε r data pole b hε x₀ z hz,
      data.χ.left_inv (data.closedBall_subset_source _ hz.2.1.le)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cocoreLevelChartInverse_val hk c ε r data pole b hε x₀ z hz]
    exact data.χ.map_source (data.closedBall_subset_source _ hz.2.1.le)
  · exact hχ.symm ▸ hz.2.1
  · exact hχ.symm ▸ hz.2.2
  · change inner ℝ pole.val
      (cocoreCoordinates hk ε r
        (data.χ.symm (cocoreLevelChartInverse hk c ε r data pole b x₀ z).val)).1 ≠ 1
    rw [cocoreLevelChart_inverse_coordinates hk c ε r data pole b hε hr x₀ z hz]
    exact (cellBoundaryChart_source_iff k pole _).mp
      ((cellBoundaryChart k pole).map_target (by rw [cellBoundaryChart_target]; trivial))
  · rw [cocoreLevelChart_inverse_coordinates hk c ε r data pole b hε hr x₀ z hz]
    exact b.map_target hz.1

private theorem cocoreLevelChart_left_inv (hε : 0 < ε) (hr : r ≠ 0)
    (x₀ x : LevelSetSpace f (c - ε))
    (hx : x ∈ cocoreLevelChartSource hk c ε r data pole b) :
    cocoreLevelChartInverse hk c ε r data pole b x₀
      (cocoreLevelChartForward hk c ε r data pole b x) = x := by
  apply Subtype.ext
  rw [cocoreLevelChartInverse_val hk c ε r data pole b hε x₀ _
    (cocoreLevelChart_map_source hk c ε r data pole b hε hr x hx),
    cocoreLevelChart_forward_inverse hk c ε r data pole b hε hr x hx,
    data.χ.right_inv hx.1]

private theorem cocoreLevelChart_right_inv (hε : 0 < ε) (hr : r ≠ 0)
    (x₀ : LevelSetSpace f (c - ε)) (z : Q)
    (hz : z ∈ cocoreLevelChartTarget hk c ε r data pole b) :
    cocoreLevelChartForward hk c ε r data pole b
      (cocoreLevelChartInverse hk c ε r data pole b x₀ z) = z := by
  dsimp [cocoreLevelChartForward]
  rw [cocoreLevelChart_inverse_coordinates hk c ε r data pole b hε hr x₀ z hz]
  change (cellBoundaryChartValue k pole ((cellBoundaryChart k pole).symm z.1).val,
    b (b.symm z.2)) = z
  rw [cellBoundaryChartValue_apply,
    (cellBoundaryChart k pole).right_inv (by rw [cellBoundaryChart_target]; trivial),
    b.right_inv hz.1]

private theorem continuousOn_cocoreLevelChartForward (hε : 0 < ε) :
    ContinuousOn (cocoreLevelChartForward hk c ε r data pole b)
      (cocoreLevelChartSource hk c ε r data pole b) := by
  have hχ : ContinuousOn (fun x : LevelSetSpace f (c - ε) => data.χ.symm x.val)
      (cocoreLevelChartSource hk c ε r data pole b) :=
    data.χ.continuousOn_invFun.comp continuous_subtype_val.continuousOn
      (fun x hx => hx.1)
  have hc := (contDiff_cocoreCoordinates hk ε r hε).continuous.comp_continuousOn hχ
  exact ((contDiffOn_cellBoundaryChartValue k pole).continuousOn.comp hc.fst
    (fun x hx => hx.2.2.2.1)).prodMk
    (b.continuousOn.comp hc.snd (fun x hx => hx.2.2.2.2))

private theorem continuousOn_cocoreLevelChartInverse (hε : 0 < ε)
    (hb : ContDiffOn ℝ ∞ b.symm b.target) (x₀ : LevelSetSpace f (c - ε)) :
    ContinuousOn (cocoreLevelChartInverse hk c ε r data pole b x₀)
      (cocoreLevelChartTarget hk c ε r data pole b) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  have hi : ContinuousOn (cocoreLevelChartInvPoint hk ε r pole b)
      (cocoreLevelChartTarget hk c ε r data pole b) :=
    (contDiffOn_cocoreLevelChartInvPoint hk ε r pole b hε hb).continuousOn.mono
      (fun z hz => hz.1)
  have h : ContinuousOn (fun z => data.χ (cocoreLevelChartInvPoint hk ε r pole b z))
      (cocoreLevelChartTarget hk c ε r data pole b) :=
    data.χ.continuousOn.comp hi (fun z hz => data.closedBall_subset_source _ hz.2.1.le)
  exact h.congr (fun z hz => cocoreLevelChartInverse_val hk c ε r data pole b hε x₀ z hz)

private def cocoreLevelChart (hε : 0 < ε) (hr : r ≠ 0)
    (hb : ContDiffOn ℝ ∞ b.symm b.target) (x₀ : LevelSetSpace f (c - ε)) :
    OpenPartialHomeomorph (LevelSetSpace f (c - ε)) Q where
  toFun := cocoreLevelChartForward hk c ε r data pole b
  invFun := cocoreLevelChartInverse hk c ε r data pole b x₀
  source := cocoreLevelChartSource hk c ε r data pole b
  target := cocoreLevelChartTarget hk c ε r data pole b
  map_source' := cocoreLevelChart_map_source hk c ε r data pole b hε hr
  map_target' := cocoreLevelChart_map_target hk c ε r data pole b hε hr x₀
  left_inv' := cocoreLevelChart_left_inv hk c ε r data pole b hε hr x₀
  right_inv' := cocoreLevelChart_right_inv hk c ε r data pole b hε hr x₀
  open_source := isOpen_cocoreLevelChartSource hk c ε r data pole b hε
  open_target := isOpen_cocoreLevelChartTarget hk c ε r data pole b hε hb
  continuousOn_toFun := continuousOn_cocoreLevelChartForward hk c ε r data pole b hε
  continuousOn_invFun := continuousOn_cocoreLevelChartInverse hk c ε r data pole b hε hb x₀

variable [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
  (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)

private theorem contMDiffOn_cocoreLevelChartForward (hε : 0 < ε)
    (hb : ContDiffOn ℝ ∞ b b.source) :
    letI := manifoldLevelSetChartedSpace I f (c - ε) hf hreg
    ContMDiffOn 𝓘(ℝ, MorseModel m) 𝓘(ℝ, Q) ∞
      (cocoreLevelChartForward hk c ε r data pole b)
      (cocoreLevelChartSource hk c ε r data pole b) := by
  let _ := manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  have hχ : ContMDiffOn 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel (m + 1)) ∞
      (fun x : LevelSetSpace f (c - ε) => data.χ.symm x.val)
      (cocoreLevelChartSource hk c ε r data pole b) := by
    apply data.symm_contMDiffOn.comp
      (contMDiff_levelSetInclusion I f (c - ε) hf hreg).contMDiffOn
    intro x hx
    exact ⟨data.χ.symm x.val, by simpa [Metric.mem_ball, dist_eq_norm] using hx.2.2.1,
      data.χ.right_inv hx.1⟩
  have hc := (contDiff_cocoreCoordinates hk ε r hε).contMDiff.comp_contMDiffOn hχ
  have hu : ContMDiffOn 𝓘(ℝ, MorseModel m) (𝓡 k) ∞
      (fun x : LevelSetSpace f (c - ε) =>
        (cocoreCoordinates hk ε r (data.χ.symm x.val)).1)
      (cocoreLevelChartSource hk c ε r data pole b) :=
    contDiff_fst.contMDiff.comp_contMDiffOn hc
  have hv : ContMDiffOn 𝓘(ℝ, MorseModel m) (𝓡 (m + 1 - k)) ∞
      (fun x : LevelSetSpace f (c - ε) =>
        (cocoreCoordinates hk ε r (data.χ.symm x.val)).2)
      (cocoreLevelChartSource hk c ε r data pole b) :=
    contDiff_snd.contMDiff.comp_contMDiffOn hc
  change ContMDiffOn 𝓘(ℝ, MorseModel m) 𝓘(ℝ, Q) ∞
    (cocoreLevelChartForward hk c ε r data pole b)
    (cocoreLevelChartSource hk c ε r data pole b)
  apply (contMDiffOn_prod_module_iff _).mpr
  exact ⟨(contDiffOn_cellBoundaryChartValue k pole).contMDiffOn.comp hu
      (fun x hx => hx.2.2.2.1),
    hb.contMDiffOn.comp hv (fun x hx => hx.2.2.2.2)⟩

private theorem contMDiffOn_cocoreLevelChartInverse (hε : 0 < ε)
    (hb : ContDiffOn ℝ ∞ b.symm b.target) (x₀ : LevelSetSpace f (c - ε)) :
    letI := manifoldLevelSetChartedSpace I f (c - ε) hf hreg
    ContMDiffOn 𝓘(ℝ, Q) 𝓘(ℝ, MorseModel m) ∞
      (cocoreLevelChartInverse hk c ε r data pole b x₀)
      (cocoreLevelChartTarget hk c ε r data pole b) := by
  let _ := manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  apply contMDiffOn_levelSet_of_val I f (c - ε) hf hreg
    (cocoreLevelChartInverse hk c ε r data pole b x₀)
    (cocoreLevelChartTarget hk c ε r data pole b)
    (isOpen_cocoreLevelChartTarget hk c ε r data pole b hε hb)
  have hi : ContMDiffOn 𝓘(ℝ, Q) 𝓘(ℝ, MorseModel (m + 1)) ∞
      (cocoreLevelChartInvPoint hk ε r pole b)
      (cocoreLevelChartTarget hk c ε r data pole b) :=
    (contDiffOn_cocoreLevelChartInvPoint hk ε r pole b hε hb).contMDiffOn.mono
      (fun z hz => hz.1)
  have h : ContMDiffOn 𝓘(ℝ, Q) I ∞
      (fun z => data.χ (cocoreLevelChartInvPoint hk ε r pole b z))
      (cocoreLevelChartTarget hk c ε r data pole b) :=
    data.contMDiffOn.comp hi
      (fun z hz => by simpa [Metric.mem_ball, dist_eq_norm] using hz.2.2)
  exact h.congr (fun z hz => cocoreLevelChartInverse_val hk c ε r data pole b hε x₀ z hz)

end LevelChart

private def cocoreChartEquiv {m k : ℕ} (hk : k ≤ m + 1)
    [NeZero k] [NeZero (m + 1 - k)] :
    (EuclideanSpace ℝ (Fin (k - 1)) ×
      EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) ≃L[ℝ] MorseModel m :=
  (LinearEquiv.ofFinrankEq _ _ (by
    have hkpos := NeZero.pos k
    have hlpos := NeZero.pos (m + 1 - k)
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin, MorseModel,
      Module.finrank_pi]
    omega)).toContinuousLinearEquiv

theorem isSmoothEmbedding_cocoreAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r : ℝ) {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.smoothRadius)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    letI := attachingRegionChartedSpace k (m + 1 - k)
    letI := manifoldLevelSetChartedSpace I f (c - ε) hf hreg
    Manifold.IsSmoothEmbedding
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      𝓘(ℝ, MorseModel m) ∞ (cocoreAttachingEmbedding hk c ε r data hε hεr.le) := by
  classical
  let _ := cellBoundaryChartedSpace k
  let _ := cellBoundaryIsManifold k
  let _ := closedCellChartedSpace (m + 1 - k)
  let _ := attachingRegionChartedSpace k (m + 1 - k)
  let _ := attachingRegionIsManifold k (m + 1 - k)
  let _ := manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  let _ := manifoldLevelSetIsManifold I f (c - ε) hf hreg
  let Iatt := (𝓡 (k - 1)).prod
    (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
  let Q := EuclideanSpace ℝ (Fin (k - 1)) ×
    EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))
  let f₀ := cocoreAttachingEmbedding hk c ε r data hε hεr.le
  refine ⟨?_, isEmbedding_cocoreAttachingEmbedding hk c ε r data hε hr hεr.le⟩
  apply Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1})
  intro p
  obtain ⟨b, hb, hb', hbp, hbval⟩ := exists_closedCellChart_extension (m + 1 - k) p.2
  let d := chartAt (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
    (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) p
  let e := cocoreLevelChart hk c ε r data (-p.1) b hε hr hb' (f₀ p)
  let L := cocoreChartEquiv hk
  let ψ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hsource : ψ.source = e.source := by simp [ψ]
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, MorseModel m) ∞
      (LevelSetSpace f (c - ε)) := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel m) ∞ (L ∘ e) ψ.source
      rw [hsource]
      exact L.contDiff.contMDiff.comp_contMDiffOn
        (contMDiffOn_cocoreLevelChartForward hk c ε r data (-p.1) b hf hreg hε hb)
    · change ContMDiffOn 𝓘(ℝ, MorseModel m) 𝓘(ℝ, MorseModel m) ∞ (e.symm ∘ L.symm) ψ.target
      apply (contMDiffOn_cocoreLevelChartInverse hk c ε r data (-p.1) b
        hf hreg hε hb' (f₀ p)).comp L.symm.contDiff.contMDiff.contMDiffOn
      intro z hz
      exact hz.2
  have hvalue : ∀ q : AttachingRegion k (m + 1 - k), ψ (f₀ q) = L ((d.extend Iatt) q) := by
    intro q
    change L (cocoreLevelChartForward hk c ε r data (-p.1) b (f₀ q)) = _
    rw [cocoreLevelChartForward_cocore hk c ε r data (-p.1) b hε hr hεr.le q, hbval]
    rfl
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (contMDiff_cocoreAttachingEmbedding hk c ε r data hε hεr.le hεr' hf hreg).continuous.continuousAt
    ((ContinuousLinearEquiv.prodUnique ℝ Q PUnit).trans L) d ψ
    (mem_chart_source _ _) ?_ (IsManifold.chart_mem_maximalAtlas p) hψ
  · intro y hy
    change ψ (f₀ ((d.extend Iatt).symm y)) = L y
    rw [hvalue, (d.extend Iatt).right_inv hy]
  · rw [hsource]
    exact cocore_mem_cocoreLevelChartSource hk c ε r data (-p.1) b
      hε hr hεr hεr' p (mem_chart_source _ _) hbp

end

end DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
