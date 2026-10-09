import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SourceChartReplacement
import DifferentialGeometry.Topology.Planar.SlitRegluing

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Planar.SlitRegluing
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

private theorem slit_square_mem_iff {r : ℝ} (hr : 0 < r) (z : ℂ) :
    z ∈ scaledSquare r ↔ |z.re| ≤ r ∧ |z.im| ≤ r := by
  simp only [scaledSquare, square, mem_ofPred_eq, Complex.div_ofReal_re,
    Complex.div_ofReal_im, abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul]

private theorem slit_square_norm_le {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ scaledSquare r) : ‖z‖ ≤ 2 * r := by
  have h := (slit_square_mem_iff hr z).mp hz
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith [h.1, h.2])

private theorem slit_map_closedBall {R : ℝ} (hR : 0 < R) :
    MapsTo (scaledSlitMap (R / 4)) (Metric.closedBall (0 : ℂ) R)
      (Metric.closedBall (0 : ℂ) R) := by
  have hr : 0 < R / 4 := by linarith
  intro z hz
  by_cases hs : z ∈ scaledSquare (R / 4)
  · have hn := slit_square_norm_le hr (scaledSlitMap_mem_scaledSquare hr.ne' hs)
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  · rw [scaledSlitMap_eq_self_of_notMem hr.ne' hs]
    exact hz

/-- The old map outside the square and the actual paired slit composite on the
square glue on a finite closed cover. This uses no continuity of the raw slit
map across its internal cut. -/
private theorem slit_composite_lipschitz_ball {Y : Type*} [PseudoEMetricSpace Y]
    {f : ℂ → Y} {R : ℝ} (hR : 0 < R) {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Metric.closedBall (0 : ℂ) R))
    (hpair : ∀ t ∈ Icc (0 : ℝ) (R / 8), f (t : ℂ) = f (-(t : ℂ))) :
    ∃ C : ℝ≥0, LipschitzOnWith C (f ∘ scaledSlitMap (R / 4))
      (Metric.closedBall (0 : ℂ) R) := by
  classical
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hsq : scaledSquare r ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hn := slit_square_norm_le hr hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    dsimp [r] at hn
    linarith
  have hp : ∀ t ∈ Icc (0 : ℝ) (r / 2), f (t : ℂ) = f (-(t : ℂ)) := by
    intro t ht
    apply hpair t
    simpa only [r, div_div, show (4 : ℝ) * 2 = 8 by norm_num] using ht
  obtain ⟨L, hL⟩ := lipschitzOnWith_comp_scaledSlitMap hr (hf.mono hsq) hp
  let outer : Set ℂ := {z | r ≤ |z.re| ∨ r ≤ |z.im|}
  have hsqClosed : IsClosed (scaledSquare r) := by
    have heq : scaledSquare r = {z : ℂ | |z.re| ≤ r} ∩ {z : ℂ | |z.im| ≤ r} := by
      ext z
      exact slit_square_mem_iff hr z
    rw [heq]
    exact (isClosed_le Complex.continuous_re.abs continuous_const).inter
      (isClosed_le Complex.continuous_im.abs continuous_const)
  have houterClosed : IsClosed outer :=
    (isClosed_le continuous_const Complex.continuous_re.abs).union
      (isClosed_le continuous_const Complex.continuous_im.abs)
  have houter (z : ℂ) (hz : z ∈ outer) : scaledSlitMap r z = z := by
    by_cases hs : z ∈ scaledSquare r
    · have hs' := (slit_square_mem_iff hr z).mp hs
      apply scaledSlitMap_eq_self_on_outer hr
      rcases hz with hz | hz
      · exact Or.inl (le_antisymm hs'.1 hz)
      · exact Or.inr (le_antisymm hs'.2 hz)
    · exact scaledSlitMap_eq_self_of_notMem hr.ne' hs
  let cells : Bool → Set ℂ := fun b => if b then outer else scaledSquare r
  let constants : Bool → ℝ≥0 := fun b => if b then K else L
  have hclosed : ∀ b, IsClosed ((Subtype.val : Metric.closedBall (0 : ℂ) R → ℂ) ⁻¹'
      cells b) := by
    intro b
    cases b
    · exact hsqClosed.preimage continuous_subtype_val
    · exact houterClosed.preimage continuous_subtype_val
  have hcover : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ∃ b, z ∈ cells b := by
    intro z _
    by_cases hs : z ∈ scaledSquare r
    · exact ⟨false, hs⟩
    · refine ⟨true, ?_⟩
      change r ≤ |z.re| ∨ r ≤ |z.im|
      by_cases hx : |z.re| ≤ r
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hy =>
          hs ((slit_square_mem_iff hr z).mpr ⟨hx, hy⟩))))
      · exact Or.inl (le_of_lt (lt_of_not_ge hx))
  have hcellLip : ∀ b, LipschitzOnWith (constants b) (f ∘ scaledSlitMap r)
      (Metric.closedBall (0 : ℂ) R ∩ cells b) := by
    intro b
    cases b
    · exact hL.mono inter_subset_right
    · intro z hz w hw
      change edist (f (scaledSlitMap r z)) (f (scaledSlitMap r w)) ≤ _
      rw [houter z hz.2, houter w hw.2]
      exact hf hz.1 hw.1
  exact ⟨Finset.univ.sup constants,
    DifferentialGeometry.Analysis.lipschitzOnWith_of_finite_closed_cover
      (convex_closedBall (0 : ℂ) R) cells hclosed hcover constants hcellLip⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Construct the literal finite-slit disk in the same original source patch.
The single supplied straightening is only Lipschitz at the center. The chart
used for global pasting is the original C1 inverse coordinate and a dilation.
The output records the exact area subtraction identity; its finite-piece area
equality and the later fold shortening are separate receiving statements. -/
theorem exists_actual_branch_slit_filling
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (e S : OpenPartialHomeomorph ℂ ℂ) {R : ℝ} (hR : 0 < R)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (heSource : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (heBall : Metric.closedBall (0 : ℂ) R ⊆ e.target)
    (hSnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖S z‖ = ‖z‖ ∧ ‖S.symm z‖ = ‖z‖ ∧
      S.symm (S z) = z ∧ S (S.symm z) = z)
    {K J : ℝ≥0}
    (hSLip : LipschitzOnWith K (S : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hSiLip : LipschitzOnWith J (S.symm : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hpair : ∀ t ∈ Icc (0 : ℝ) R,
      diskExtension u (e.symm (S (t : ℂ))) =
        diskExtension u (e.symm (S (-(t : ℂ))))) :
    ∃ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
      (d v : C(closedDisk, M)) (C A : ℝ≥0),
      (∀ z, χ z = e.symm ((R : ℂ) * z)) ∧
      (∀ z, χ.symm z = e z / (R : ℂ)) ∧
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        S (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z))) ∈ Metric.closedBall (0 : ℂ) R) ∧
      (∀ z : closedDisk, d z = diskExtension u
        (e.symm (S (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z)))))) ∧
      (∀ z w, riemannianEDistOf g (d z) (d w) ≤ (C : ℝ≥0∞) * edist z w) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) 1,
        diskExtension d z = diskExtension u (χ z)) ∧
      Set.range d ⊆ Set.range u ∧
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (A : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ Set.range u ∧
      (∀ z : closedDisk, (z : ℂ) ∈ χ '' Metric.closedBall (0 : ℂ) 1 →
        v z = diskExtension d (χ.symm z)) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ interior (χ '' Metric.closedBall (0 : ℂ) 1) →
        v z = u z) ∧
      riemannianDiskArea g v = riemannianDiskArea g u -
        riemannianArea g (diskExtension u) (χ '' Metric.closedBall (0 : ℂ) 1) +
        riemannianDiskArea g d := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hscale : MapsTo (fun z : ℂ => (R : ℂ) * z) (Metric.closedBall (0 : ℂ) 1)
      (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    rw [norm_mul, hnormR]
    nlinarith
  have hSmap : MapsTo (S : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R)
      (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, (hSnorm z hz).1] using hz
  have hSimap : MapsTo (S.symm : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R)
      (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, (hSnorm z hz).2.1] using hz
  let χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1 :=
    { toFun := fun z => e.symm ((R : ℂ) * z)
      invFun := fun z => e z / (R : ℂ)
      source := (fun z : ℂ => (R : ℂ) * z) ⁻¹' e.target
      target := e.source
      map_source' := fun _ hz => e.map_target hz
      map_target' := by
        intro z hz
        change (R : ℂ) * (e z / (R : ℂ)) ∈ e.target
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hRc]
        exact e.map_source hz
      left_inv' := by
        intro z hz
        rw [e.right_inv hz, mul_div_cancel_left₀ _ hRc]
      right_inv' := by
        intro z hz
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hRc]
        exact e.left_inv hz
      open_source := e.open_target.preimage (continuous_const.mul continuous_id)
      open_target := e.open_source
      contMDiffOn_toFun :=
        (hei.comp (contDiff_const.mul contDiff_id).contDiffOn (fun _ hz => hz)).contMDiffOn
      contMDiffOn_invFun := (he.div_const (R : ℂ)).contMDiffOn }
  have hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source := fun _ hz => heBall (hscale hz)
  have hχinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact heSource (e.map_target (heBall (hscale hz)))
  let f : ℂ → M := fun z => diskExtension u (e.symm (S z))
  obtain ⟨B, hB⟩ := hei.exists_lipschitzOnWith_of_isCompact e.open_target
    (isCompact_closedBall (0 : ℂ) R) heBall
  have hU : LipschitzWith L (diskExtension u) := diskExtension_riemannian_lipschitz g huLip
  have hf : LipschitzOnWith (L * (B * K)) f (Metric.closedBall (0 : ℂ) R) :=
    hU.comp_lipschitzOnWith (hB.comp hSLip hSmap)
  have hpair' : ∀ t ∈ Icc (0 : ℝ) (R / 8), f (t : ℂ) = f (-(t : ℂ)) := by
    intro t ht
    exact hpair t ⟨ht.1, by linarith [ht.2]⟩
  obtain ⟨Bq, hq⟩ := slit_composite_lipschitz_ball hR hf hpair'
  have hmul : LipschitzWith ‖(R : ℂ)‖₊ (fun z : ℂ => (R : ℂ) * z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(R : ℂ) * z - (R : ℂ) * w‖ ≤ ‖(R : ℂ)‖ * ‖z - w‖
    rw [← mul_sub, norm_mul]
  let D : ℂ → M := fun z => f (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z)))
  have hD : LipschitzOnWith (Bq * (J * ‖(R : ℂ)‖₊)) D (Metric.closedBall (0 : ℂ) 1) :=
    hq.comp (hSiLip.comp hmul.lipschitzOnWith hscale) (fun _ hz => hSimap (hscale hz))
  let d : C(closedDisk, M) := ⟨fun z => D z, hD.to_restrict.continuous⟩
  have hdLip : ∀ z w : closedDisk, riemannianEDistOf g (d z) (d w) ≤
      ((Bq * (J * ‖(R : ℂ)‖₊) : ℝ≥0) : ℝ≥0∞) * edist z w :=
    fun z w => hD z.property w.property
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension d z = diskExtension u (χ z) := by
    intro z hz
    have hzBall := Metric.sphere_subset_closedBall hz
    have hzNorm : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hn : ‖S.symm ((R : ℂ) * z)‖ = R := by
      rw [(hSnorm _ (hscale hzBall)).2.1, norm_mul, hnormR, hzNorm, mul_one]
    have hout : S.symm ((R : ℂ) * z) ∉ scaledSquare (R / 4) := by
      intro hin
      have hb := slit_square_norm_le (by linarith : 0 < R / 4) hin
      rw [hn] at hb
      linarith
    rw [diskExtension_coe d ⟨z, hzBall⟩]
    change diskExtension u (e.symm (S (scaledSlitMap (R / 4)
      (S.symm ((R : ℂ) * z))))) = diskExtension u (e.symm ((R : ℂ) * z))
    rw [scaledSlitMap_eq_self_of_notMem (by linarith : R / 4 ≠ 0) hout,
      (hSnorm _ (hscale hzBall)).2.2.2]
  have hdRange : Set.range d ⊆ Set.range u := by
    rintro _ ⟨z, rfl⟩
    exact mem_range_self (diskRetraction
      (e.symm (S (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z))))))
  obtain ⟨v, A, hvLip, hvTrace, hvRange, hvIn, hvOut, hvArea⟩ :=
    exists_sourceChart_disk_replacement g u d huLip hdLip χ le_rfl hχsrc hχinside
      hboundary (Set.Subset.rfl : Set.range u ⊆ Set.range u) hdRange
  exact ⟨χ, d, v, Bq * (J * ‖(R : ℂ)‖₊), A, fun _ => rfl, fun _ => rfl,
    hχsrc, hχinside,
    (fun _ hz => hSmap (slit_map_closedBall hR (hSimap (hscale hz)))),
    fun _ => rfl, hdLip, hboundary, hdRange,
    hvLip, hvTrace, hvRange, hvIn, hvOut, hvArea⟩

end DifferentialGeometry.Geometry
