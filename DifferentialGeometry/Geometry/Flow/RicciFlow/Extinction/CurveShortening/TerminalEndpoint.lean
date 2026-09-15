import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothLimits
import DifferentialGeometry.Analysis.Calculus.TimeJet.ClosedJetEvolution
import DifferentialGeometry.Topology.Manifold.SpatialJets
import DifferentialGeometry.Topology.Manifold.EndpointRegularity
import DifferentialGeometry.Topology.Manifold.LeftInverse
import DifferentialGeometry.Topology.Order.Interval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ChartEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SpatialDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SpeedContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TerminalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContinuationFrontier

section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothTubularRetraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contMDiffOn_of_contDiffOn_comp {N : ℕ}
    {e : SmoothLoopEmbedding (I := I) (Q := Q) N} (R : SmoothTubularRetraction e)
    {g : F → Q} {s : Set F} {n : ℕ∞ω} (hn : n ≤ ∞)
    (hg : ContDiffOn ℝ n (e.map ∘ g) s) : ContMDiffOn 𝓘(ℝ, F) I n g s := by
  exact R.leftInverse.contMDiffOn_of_comp (R.smoothOn.of_le hn) hg.contMDiffOn
    (fun x _ => R.range_subset (Set.mem_range_self (g x)))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothTubularRetraction

end

section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [CompactSpace Q] [Nonempty Q]

private theorem exists_smoothLoopEmbedding_with_retraction :
    ∃ N : ℕ, ∃ e : SmoothLoopEmbedding (I := I) (Q := Q) N,
      Nonempty (SmoothTubularRetraction e) := by
  obtain ⟨N, ⟨e⟩⟩ := smoothLoopEmbedding_exists (I := I) (Q := Q)
  obtain ⟨r, U, hU, hrange, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction e.smooth
      e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  exact ⟨N, e, ⟨⟨U, hU, hrange, r, hr, hleft⟩⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end


noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_embedded_spatial_endpoint_extension
    (B : RicciBackground (I := I) (M := M) D a b) {T s : ℝ}
    (hTb : T ≤ b) (has : a < s) (hsT : s < T)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : M → F)
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hinj : Function.Injective f) :
    ∃ closed : CurveMap M,
      (∀ z t, t ∈ Ico a T → closed z t = c z t) ∧
      Continuous (fun z => closed z T) ∧
      TendstoUniformly (fun t x => f (c.lift x t))
        (fun x => f (closed.lift x T)) (𝓝[<] T) ∧
      (∀ z, Tendsto (c z) (𝓝[<] T) (𝓝 (closed z T))) ∧
      (∀ t ∈ Icc s T, ContDiffOn ℝ (∞ : WithTop ℕ∞)
        (fun x : ℝ => f (closed.lift x t)) Set.univ) ∧
      (∀ r : ℕ, ContinuousOn
        (fun p : ℝ × ℝ => iteratedFDeriv ℝ r (fun x => f (closed.lift x p.1)) p.2)
        (Icc s T ×ˢ Set.univ)) := by
  have haT : a < T := has.trans hsT
  have hsub : Ico s T ⊆ Ico a T := fun t ht => ⟨has.le.trans ht.1, ht.2⟩
  have hg := metricTensor_cont_restrict_of_metricFamilySmoothOn B.family.metric B.smooth
    (fun t (ht : t ∈ Icc a T) => D.regular_subset (B.regular ⟨ht.1, ht.2.trans hTb⟩))
  obtain ⟨cT, hcTlim, hcTpoint⟩ :=
    hc.exists_continuous_terminal_curve haT hg (hf.of_le (by norm_num)) hinj hcurv
  let closed : CurveMap M := fun z t => if t < T then c z t else cT z
  have heq : ∀ z t, t ∈ Ico a T → closed z t = c z t := by
    intro z t ht
    simp [closed, ht.2]
  have hpoint : ∀ x : ℝ, x ∈ Set.univ →
      Tendsto (fun t => f (closed.lift x t)) (𝓝[Ico s T] T)
        (𝓝 (f (closed.lift x T))) := by
    intro x _
    have hct := hcTpoint (x : AddCircle (1 : ℝ))
    have hft : Tendsto (fun t => f (c.lift x t)) (𝓝[<] T)
        (𝓝 (f (cT (x : AddCircle (1 : ℝ))))) :=
      (hf.continuous.continuousAt.tendsto.comp hct)
    have heqT : closed.lift x T = cT (x : AddCircle (1 : ℝ)) := by simp [closed, CurveMap.lift]
    rw [heqT]
    apply (hft.mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [closed, CurveMap.lift, if_pos ht.2]
  have hGtime : ∀ x : ℝ, x ∈ Set.univ →
      ContinuousOn (fun t => f (closed.lift x t)) (Ico s T) := by
    intro x _
    have ht := hf.continuous.comp_continuousOn
      ((c.time_slice_contMDiffOn (Ico a T) hc.smooth x).continuousOn.mono hsub)
    exact ht.congr (fun t htm => by simp [closed, CurveMap.lift, htm.2])
  have hGs : ∀ t ∈ Ico s T, ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fun x : ℝ => f (closed.lift x t)) Set.univ := by
    intro t ht
    have hsmooth := c.space_slice_contMDiffOn (Ico a T) hc.smooth t
      ⟨has.le.trans ht.1, ht.2⟩
    have hsm := (hf.comp (contMDiffOn_univ.mp hsmooth)).contDiff.contDiffOn (s := Set.univ)
    simpa only [Function.comp_def, closed, CurveMap.lift, if_pos ht.2] using hsm
  have hbdd : ∀ r : ℕ, ∀ Q : Set ℝ, IsCompact Q → Q ⊆ Set.univ →
      ∃ C : ℝ, ∀ t ∈ Ico s T, ∀ x ∈ Q,
        ‖iteratedFDeriv ℝ r (fun y : ℝ => f (closed.lift y t)) x‖ ≤ C := by
    intro r Q hQ hQsub
    obtain ⟨C, hC, hbound⟩ := c.exists_iteratedDeriv_comp_lift_bounds_on_Ico_of_curvature_le
      B haT hTb hc hcurv f hf s has r
    refine ⟨C, fun t ht x hx => ?_⟩
    rw [show (fun y : ℝ => f (closed.lift y t)) = (fun y => f (c.lift y t)) by
      funext y; simp [closed, CurveMap.lift, ht.2]]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hbound x t ht
  obtain ⟨hsmooth, hjets⟩ :=
    DifferentialGeometry.CheegerGromovCompactness.contDiffOn_and_continuousOn_spatial_iteratedFDeriv_Icc
      (show s < T from hsT) (isOpen_univ) (fun t x => f (closed.lift x t)) hGtime hpoint hGs hbdd
  refine ⟨closed, heq, ?_, ?_, ?_, hsmooth, hjets⟩
  · simpa only [closed, lt_self_iff_false, if_false] using cT.continuous
  · simpa only [closed, CurveMap.lift, lt_self_iff_false, if_false] using hcTlim
  · intro z
    simpa only [closed, lt_self_iff_false, if_false] using hcTpoint z

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_spatially_smooth_immersed_endpoint_extension
    (B : RicciBackground (I := I) (M := M) D a b) {T s : ℝ}
    (hTb : T ≤ b) (has : a < s) (hsT : s < T)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := M) N)
    (R : SmoothTubularRetraction (I := I) (Q := M) e) :
    ∃ closed : CurveMap M,
      (∀ z t, t ∈ Ico a T → closed z t = c z t) ∧
      Continuous (fun z => closed z T) ∧
      TendstoUniformly (fun t x => e.map (c.lift x t))
        (fun x => e.map (closed.lift x T)) (𝓝[<] T) ∧
      (∀ z, Tendsto (c z) (𝓝[<] T) (𝓝 (closed z T))) ∧
      (∀ t ∈ Icc s T, ContDiff ℝ ∞ (fun x : ℝ => e.map (closed.lift x t))) ∧
      (∀ r : ℕ, ContinuousOn
        (fun p : ℝ × ℝ => iteratedFDeriv ℝ r (fun x => e.map (closed.lift x p.1)) p.2)
        (Icc s T ×ˢ univ)) ∧
      (∀ t ∈ Icc s T, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => closed.lift x t)) ∧
      closed.ImmersedOn (I := I) (Icc s T) := by
  obtain ⟨closed, heq, hcontT, hunif, hpoint, hsmooth, hjets⟩ :=
    exists_embedded_spatial_endpoint_extension B hTb has hsT c hc hcurv e.map
      e.smooth e.isClosedEmbedding.injective
  have hsm : ∀ t ∈ Icc s T,
      ContDiff ℝ ∞ (fun x : ℝ => e.map (closed.lift x t)) :=
    fun t ht => contDiffOn_univ.mp (hsmooth t ht)
  have hman : ∀ t ∈ Icc s T,
      ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => closed.lift x t) := by
    intro t ht
    exact contMDiffOn_univ.mp
      (R.contMDiffOn_of_contDiffOn_comp le_rfl (hsmooth t ht))
  obtain ⟨m, C, hm, hC, hbound⟩ :=
    exists_speed_bounds_of_curvature_le_Ico B (has.trans hsT) hTb c hc hcurv
  have hslice : ∀ t ∈ Icc s T, Differentiable ℝ
      (fun x => e.map (closed.lift x t)) :=
    fun t ht => (hsm t ht).differentiable (by simp)
  have hval : ContinuousOn
      (fun p : ℝ × ℝ => e.map (closed.lift p.1 p.2)) (univ ×ˢ Icc s T) := by
    have h' := (hjets 0).comp
      (continuous_swap.continuousOn (s := univ ×ˢ Icc s T))
      (by intro p hp; exact ⟨hp.2, hp.1⟩)
    simpa [Function.comp_def, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.apply (𝕜 := ℝ) (E := fun _ : Fin 0 => ℝ)
        (F := EuclideanSpace ℝ (Fin N)) 0).continuous.comp_continuousOn h'
  have hder : ContinuousOn
      (fun p : ℝ × ℝ => deriv (fun x => e.map (closed.lift x p.2)) p.1)
      (univ ×ˢ Icc s T) := by
    have h' := (hjets 1).comp
      (continuous_swap.continuousOn (s := univ ×ˢ Icc s T))
      (by intro p hp; exact ⟨hp.2, hp.1⟩)
    simpa [Function.comp_def, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_one_apply, fderiv_apply_one_eq_deriv] using
      (ContinuousMultilinearMap.apply (𝕜 := ℝ) (E := fun _ : Fin 1 => ℝ)
        (F := EuclideanSpace ℝ (Fin N)) 1).continuous.comp_continuousOn h'
  refine ⟨closed, heq, hcontT, hunif, hpoint, hsm, hjets, hman, ?_⟩
  apply immersedOn_Icc_of_leftInverse_of_speed_lower_bound B.smooth hsT
    (fun t ht => D.regular_subset (B.regular ⟨has.le.trans ht.1, ht.2.trans hTb⟩))
    e.map R.retract R.isOpen_neighborhood (R.smoothOn.of_le (by simp))
    (fun x t _ => R.range_subset ⟨closed.lift x t, rfl⟩)
    (fun x t _ => R.leftInverse (closed.lift x t)) hslice hval hder hm
  intro x t ht
  have hat : t ∈ Ico a T := ⟨has.le.trans ht.1, ht.2⟩
  have hmaps : ∀ y : ℝ, closed.lift y t = c.lift y t := fun y => heq y t hat
  have hX := X_congr (I := I) hmaps x
  have hs : closed.speed B.family.metric x t = c.speed B.family.metric x t := by
    unfold CurveMap.speed
    rw [hmaps x, hX]
  rw [hs]
  exact (hbound x t hat).1

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

end


noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [I.Boundaryless]
    {D : Geometry.Curvature.RealTimeInterval} {a T : ℝ}

namespace CurveMap

theorem isSolutionOn_Icc_of_Ico
    (haT : a < T) (g : ℝ → SmoothRiemannianMetric I M)
    (hG : Geometry.Curvature.MetricFamilySmoothOn (I := I) (M := M) D g)
    (hreg : Icc a T ⊆ D.regular)
    {c c' : CurveMap M}
    (hsol : c.IsSolutionOn (I := I) g (Ico a T))
    (hsm : c'.SmoothOn (I := I) (Icc a T))
    (himm : c'.ImmersedOn (I := I) (Icc a T))
    (heq : ∀ x t, t ∈ Ico a T → c'.lift x t = c.lift x t) :
    c'.IsSolutionOn (I := I) g (Icc a T) := by
  have hJun : UniqueDiffOn ℝ (Icc a T) := uniqueDiffOn_Icc haT
  have hsol' : c'.IsSolutionOn (I := I) g (Ico a T) := isSolutionOn_congr heq hsol
  have hvel := Field.smoothOn_velocity c' hsm hJun
  have hcurv := Field.smoothOn_curvatureVector g hG hreg hJun c' hsm himm
  refine ⟨hsm, himm, ?_⟩
  intro x t ht
  let V : ℝ → TangentBundle I M :=
    fun s => ⟨c'.lift x s, c'.velocity (I := I) (Icc a T) x s⟩
  let W : ℝ → TangentBundle I M := fun s => ⟨c'.lift x s, c'.curvatureVector g x s⟩
  have hvcont : ContinuousOn V (Icc a T) :=
    hvel.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun s hs => ⟨mem_univ x, hs⟩)
  have hwcont : ContinuousOn W (Icc a T) :=
    hcurv.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun s hs => ⟨mem_univ x, hs⟩)
  have hprior : EqOn V W (Ico a T) := by
    intro s hs
    have hMD : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c'.lift x) (Icc a T) s :=
      (c'.time_slice_contMDiffWithinAt (I := I) (Icc a T) hsm x s
        (Ico_subset_Icc_self hs)).mdifferentiableWithinAt (by simp)
    have hmem : Icc a T ∈ 𝓝[Ico a T] s :=
      Filter.mem_of_superset self_mem_nhdsWithin Ico_subset_Icc_self
    have hder := hMD.mfderivWithin_mono_of_mem_nhdsWithin
      (((uniqueDiffOn_Ico a T) s hs).uniqueMDiffWithinAt) hmem
    have hv : c'.velocity (I := I) (Ico a T) x s =
        c'.velocity (I := I) (Icc a T) x s := congrArg (fun L => L 1) hder
    have h := hv.symm.trans (hsol'.equation x s hs)
    exact congrArg (fun v : TangentSpace I (c'.lift x s) =>
      (⟨c'.lift x s, v⟩ : TangentBundle I M)) h
  have hext := hprior.of_subset_closure hvcont hwcont Ico_subset_Icc_self
    (by rw [closure_Ico haT.ne])
  have htotal := hext ht
  exact congrArg (fun z : TangentBundle I M => z.2) htotal

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {c : CurveMap M} {a b : ℝ}

theorem smoothOn_Icc_of_Ico_of_locally_Icc
    (hc : c.SmoothOn (I := I) (Ico a b))
    (hb : ∀ x : ℝ, ∃ s < b, ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun p : ℝ × ℝ => c.lift p.1 p.2) (V ×ˢ Icc s b)) :
    c.SmoothOn (I := I) (Icc a b) := by
  have hc' : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ Ico a b) := by
    rw [CurveMap.SmoothOn] at hc
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hc
    exact hc
  have h := hc'.prod_Icc_of_prod_Ico_of_locally_Icc (fun x _ => ?_)
  · rw [CurveMap.SmoothOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  · obtain ⟨s, hsb, V, hV, hxV, hcV⟩ := hb x
    refine ⟨s, hsb, V, hV, hxV, ?_⟩
    rw [univ_inter]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcV
    exact hcV

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem contMDiffOn_Icc_prod_of_chart_spatial_jets
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {a s T : ℝ} (has : a ≤ s) (hsT : s < T)
    (hreg : Icc s T ⊆ D.regular) {c d : CurveMap M}
    (hc : c.IsSolutionOn g (Ico a T))
    (heq : ∀ z t, t ∈ Ico a T → d z t = c z t)
    (β : M) {V : Set ℝ} (hV : IsOpen V)
    (hi : ∀ x ∈ V, ∀ t ∈ Icc s T, d.X (I := I) x t ≠ 0)
    (hchart : MapsTo (fun p : ℝ × ℝ => d.lift p.2 p.1)
      (Icc s T ×ˢ V) (extChartAt I β).source)
    (hGs : ∀ t ∈ Icc s T, ContDiffOn ℝ ∞
      (fun x => extChartAt I β (d.lift x t)) V)
    (hjets : ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => iteratedFDeriv ℝ r
        (fun x => extChartAt I β (d.lift x p.1)) p.2) (Icc s T ×ˢ V)) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => d.lift p.2 p.1) (Icc s T ×ˢ V) := by
  let G : ℝ → ℝ → E := fun t x => extChartAt I β (d.lift x t)
  have hmap : MapsTo (fun p : ℝ × ℝ => (p, Analysis.jet2 (G p.1) p.2))
      (Icc s T ×ˢ V) (curveShorteningChartDomainJet D g β) := by
    intro p hp
    exact d.chartJet_mem_curveShorteningChartDomainJet β (hreg hp.1)
      (hchart hp) (hi p.2 hp.2 p.1 hp.1)
  have hpde : ∀ t ∈ Ioo s T, ∀ x ∈ V,
      HasDerivAt (fun τ => G τ x)
        (curveShorteningChartRhsJet g β ((t, x), Analysis.jet2 (G t) x)) t := by
    intro t ht x hx
    have htold : t ∈ Ico a T := ⟨has.trans ht.1.le, ht.2⟩
    have hloc : Ico a T ∈ 𝓝 t := Ico_mem_nhds (has.trans_lt ht.1) ht.2
    have hslice : (fun y => extChartAt I β (d.lift y t)) =
        (fun y => extChartAt I β (c.lift y t)) := by
      funext y
      rw [show d.lift y t = c.lift y t from heq (y : AddCircle (1 : ℝ)) t htold]
    have hsrc : c.lift x t ∈ (extChartAt I β).source := by
      rw [← show d.lift x t = c.lift x t from heq (x : AddCircle (1 : ℝ)) t htold]
      exact hchart (x := (t, x)) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
    have h := hc.hasDerivAt_chartRhsJet β x t hloc hsrc
    have hev : (fun τ => G τ x) =ᶠ[𝓝 t]
        (fun τ => extChartAt I β (c.lift x τ)) := by
      filter_upwards [hloc] with τ hτ
      dsimp [G]
      rw [show d.lift x τ = c.lift x τ from heq (x : AddCircle (1 : ℝ)) τ hτ]
    dsimp only [G]
    rw [hslice]
    exact h.congr_of_eventuallyEq hev
  have hboot := Analysis.contDiffOn_and_equation_Icc_of_time_dependent_spatial_jets
    G s T hsT V hV (curveShorteningChartRhsJet g β)
    (curveShorteningChartDomainJet D g β) (isOpen_curveShorteningChartDomainJet hg β)
    (contDiffOn_curveShorteningChartRhsJet hg β) hmap hGs hjets hpde
  have hback := (contMDiffOn_extChartAt_symm (I := I) β).comp hboot.1.contMDiffOn
    (fun p hp => (extChartAt I β).mapsTo (hchart hp))
  exact hback.congr (fun p hp => ((extChartAt I β).left_inv (hchart hp)).symm)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Extinction.Width

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isSolutionOn_Icc_of_embedded_spatial_jets
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {a s T : ℝ} (has : a ≤ s) (hsT : s < T)
    (hreg : Icc a T ⊆ D.regular) {c d : CurveMap M}
    (hc : c.IsSolutionOn g (Ico a T))
    (heq : ∀ z t, t ∈ Ico a T → d z t = c z t)
    (hiT : ∀ x, d.X (I := I) x T ≠ 0)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := M) N)
    (R : SmoothTubularRetraction e)
    (hGs : ∀ t ∈ Icc s T, ContDiffOn ℝ ∞ (fun x => e.map (d.lift x t)) univ)
    (hjets : ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => iteratedFDeriv ℝ r (fun x => e.map (d.lift x p.1)) p.2)
      (Icc s T ×ˢ univ)) :
    d.IsSolutionOn g (Icc a T) := by
  have hiclosed : d.ImmersedOn (I := I) (Icc a T) := by
    intro x t ht
    by_cases hlt : t < T
    · have hXt : d.X (I := I) x t = c.X (I := I) x t :=
        X_congr (fun y => heq (y : AddCircle (1 : ℝ)) t ⟨ht.1, hlt⟩) x
      rw [hXt]
      exact hc.immersed x t ⟨ht.1, hlt⟩
    · have htT : t = T := le_antisymm ht.2 (le_of_not_gt hlt)
      rw [htT]
      exact hiT x
  have hval : ContinuousOn (fun p : ℝ × ℝ => e.map (d.lift p.2 p.1))
      (Icc s T ×ˢ univ) := by
    have h := (continuousMultilinearCurryFin0 ℝ ℝ (EuclideanSpace ℝ (Fin N))).continuous.comp_continuousOn
      (hjets 0)
    exact h.congr (fun p _ => rfl)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => d.lift p.2 p.1) (Icc s T ×ˢ univ) := by
    have h := R.smoothOn.continuousOn.comp hval
      (fun p _ => R.range_subset (mem_range_self (d.lift p.2 p.1)))
    exact h.congr (fun p _ => (R.leftInverse (d.lift p.2 p.1)).symm)
  have hsold : d.SmoothOn (I := I) (Ico a T) := by
    apply hc.smooth.congr
    intro p hp
    exact heq (p.1 : AddCircle (1 : ℝ)) p.2 hp.2
  have hsclosed : d.SmoothOn (I := I) (Icc a T) := by
    apply smoothOn_Icc_of_Ico_of_locally_Icc hsold
    intro x
    let β : M := d.lift x T
    obtain ⟨s', hss', hs'T, V, hV, hxV, hchart⟩ :=
      hcont.exists_mapsTo_Icc_prod_nhds hsT
        (show IsOpen (extChartAt I β).source by rw [extChartAt_source]; exact (chartAt H β).open_source)
        (show d.lift x T ∈ (extChartAt I β).source by exact mem_extChartAt_source β)
    have hsub : Icc s' T ⊆ Icc s T := Icc_subset_Icc hss' le_rfl
    have hsG : ∀ t ∈ Icc s' T, ContDiffOn ℝ ∞ (fun y => e.map (d.lift y t)) V :=
      fun t ht => (hGs t (hsub ht)).mono (subset_univ V)
    have hsjet : ∀ r : ℕ, ContinuousOn
        (fun p : ℝ × ℝ => iteratedFDeriv ℝ r (fun y => e.map (d.lift y p.1)) p.2)
        (Icc s' T ×ˢ V) :=
      fun r => (hjets r).mono (Set.prod_mono hsub (subset_univ V))
    obtain ⟨hcs, hcj⟩ := Analysis.contDiffOn_and_continuousOn_spatial_iteratedFDeriv_extChartAt_of_leftInverse
      (G := fun t x => d.lift x t) (f := e.map) (r := R.retract)
      β hV R.isOpen_neighborhood R.smoothOn R.leftInverse
      (fun p _ => R.range_subset (mem_range_self (d.lift p.2 p.1))) hchart hsG hsjet
    have hlocal := contMDiffOn_Icc_prod_of_chart_spatial_jets hg (has.trans hss') hs'T
      (fun t ht => hreg ⟨has.trans (hsub ht).1, ht.2⟩) hc heq
      β hV (fun y _ t ht => hiclosed y t ⟨has.trans (hsub ht).1, ht.2⟩) hchart hcs hcj
    refine ⟨s', hs'T, V, hV, hxV, ?_⟩
    exact hlocal.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn
      (fun p hp => ⟨hp.2, hp.1⟩)
  exact isSolutionOn_Icc_of_Ico (has.trans_lt hsT) g hg hreg hc hsclosed hiclosed
    (fun x t ht => heq (x : AddCircle (1 : ℝ)) t ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Extinction.Width

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}

theorem exists_isSolutionOn_Icc_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ}
    (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    {K : ℝ} (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) :
    ∃ closed : CurveMap M,
      closed.IsSolutionOn B.family.metric (Icc a T) ∧
      ∀ z t, t ∈ Ico a T → closed z t = c z t := by
  let : Nonempty M := ⟨c 0 0⟩
  obtain ⟨N, e, ⟨R⟩⟩ := exists_smoothLoopEmbedding_with_retraction (I := I) (Q := M)
  let s : ℝ := (a + T) / 2
  have has : a < s := by dsimp [s]; linarith
  have hsT : s < T := by dsimp [s]; linarith
  obtain ⟨closed, heq, _, _, _, hGs, hjets, _, hi⟩ :=
    exists_spatially_smooth_immersed_endpoint_extension B hTb has hsT c hc hcurv e R
  refine ⟨closed, ?_, heq⟩
  exact isSolutionOn_Icc_of_embedded_spatial_jets B.smooth has.le hsT
    (fun t ht => B.regular ⟨ht.1, ht.2.trans hTb⟩) hc heq
    (fun x => hi x T ⟨hsT.le, le_rfl⟩) e R
    (fun t ht => (hGs t ht).contDiffOn) hjets

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}

theorem curveShorteningTerminalClosure_of_ricciBackground
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningTerminalClosure B := by
  intro T haT hTb c K _ hc hcurv
  exact CurveMap.exists_isSolutionOn_Icc_of_curvature_le B haT hTb c hc hcurv

theorem curveShorteningExtension_of_localWindow
    (B : RicciBackground (I := I) (M := M) D a b)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B.toSmoothMetricWindow)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B.toSmoothMetricWindow) :
    curveShorteningExtension (I := I) (M := M) B := by
  intro T haT hTb c K hK hc hcurv
  let : Nonempty M := ⟨c 0 0⟩
  obtain ⟨N, ⟨e⟩⟩ := Width.smoothLoopEmbedding_exists (I := I) (Q := M)
  exact curveShorteningExtension_of_terminalClosure_and_localWindow B
    (curveShorteningTerminalClosure_of_ricciBackground B) hwin huniq e
    T haT hTb c K hK hc hcurv

theorem curveShorteningContinuation_of_localWindow
    (B : RicciBackground (I := I) (M := M) D a b)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B.toSmoothMetricWindow)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B.toSmoothMetricWindow) :
    curveShorteningContinuation (I := I) (M := M) B :=
  (curveShorteningContinuation_iff_terminalClosure_and_extension B).mpr
    ⟨curveShorteningTerminalClosure_of_ricciBackground B,
      curveShorteningExtension_of_localWindow B hwin huniq⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
