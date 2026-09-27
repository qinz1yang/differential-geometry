import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndpoint

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

omit [IsManifold I3 ∞ W] in
theorem GlobalNeckTube.isConnected_univ (T : GlobalNeckTube W) :
    IsConnected (univ : Set W) := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  have hsource : IsConnected T.map.source := by
    rw [T.source_eq]
    exact (_root_.isConnected_univ : IsConnected (univ : Set (Sphere 2))).prod
      (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))
  have himage := hsource.image T.map T.map.contMDiffOn_toFun.continuousOn
  simpa only [T.map.toPartialEquiv.image_source_eq_target, T.target_eq] using himage

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edist_eq_ofReal_dist (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (x y : W) :
    riemannianEDistOf g x y = ENNReal.ofReal (dist x y) := by
  let : ConnectedSpace W := connectedSpace_iff_univ.mpr H.tube.isConnected_univ
  let : RiemannianBundle (fun z : W => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun z : W => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  have hfinite : riemannianEDistOf g x y ≠ ⊤ :=
    Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I3) x y
  rw [H.intrinsic, metricDistance, ENNReal.ofReal_toReal hfinite]

theorem finiteHorn_ball_subset_subend (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (i : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < delta → x ∈ H.subend i := by
  let q := H.cut_height i
  have hq : q ∈ Ioo (0 : ℝ) 1 := H.cut_height_mem i
  let S := H.tube.sectionSet q
  have hS : IsCompact S := by
    simpa only [S, GlobalNeckTube.sectionSet, Icc_self] using
      H.tube.isCompact_slab hq.1 hq.2
  have hne : S.Nonempty := by
    let p := (H.tube.map.symm (H.axial.point H.axial.length)).1
    exact ⟨H.tube.map (p, q), ⟨(p, q), ⟨mem_univ _, rfl⟩, rfl⟩⟩
  have hc : Continuous (fun z : W => dist (z : UniformSpace.Completion W) H.endpoint) :=
    (UniformSpace.Completion.continuous_coe W).dist continuous_const
  obtain ⟨z₀, _hz₀, hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
  let m := dist (z₀ : UniformSpace.Completion W) H.endpoint
  have hm : 0 < m := dist_pos.mpr (H.endpoint_missing z₀)
  obtain ⟨d, hd, hdL, htail⟩ := H.cofinal_axial i
  let s : ℝ := min d (m / 4) / 2
  have hs : 0 < s := half_pos (lt_min hd (by positivity))
  have hsd : s ≤ d := by
    have h := min_le_left d (m / 4)
    dsimp [s]
    linarith
  have hsm : s < m / 4 := by
    have h := min_le_right d (m / 4)
    dsimp [s]
    linarith
  have hsL : s ∈ Ioc (0 : ℝ) H.axial.length := ⟨hs, hsd.trans hdL⟩
  have hstart : H.tube.height (H.axial.point s) < q := by
    have h := htail s ⟨hs, hsd⟩
    rwa [H.subend_eq i] at h
  refine ⟨m / 4, by positivity, ?_⟩
  intro x hx
  by_contra hnot
  have hend : q ≤ H.tube.height x := by
    apply le_of_not_gt
    intro hlt
    apply hnot
    rw [H.subend_eq i]
    exact hlt
  have hax : dist (H.axial.point s) x < m / 2 := by
    calc
      _ = dist (H.axial.point s : UniformSpace.Completion W)
          (x : UniformSpace.Completion W) := by rw [UniformSpace.Completion.dist_eq]
      _ ≤ dist (H.axial.point s : UniformSpace.Completion W) H.endpoint +
          dist H.endpoint (x : UniformSpace.Completion W) := dist_triangle _ _ _
      _ = s + dist (x : UniformSpace.Completion W) H.endpoint := by
        rw [H.axial.radial s hsL, dist_comm H.endpoint]
      _ < m / 2 := by linarith
  have hedist : riemannianEDistOf g (H.axial.point s) x < ENNReal.ofReal (m / 2) := by
    rw [H.edist_eq_ofReal_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hax
  obtain ⟨gamma, hg0, hg1, hgsmooth, hlength⟩ := exists_lt_of_edistOf_lt g hedist
  have hh : ContinuousOn (H.tube.height ∘ gamma) (Icc (0 : ℝ) 1) :=
    H.tube.continuous_height.comp_continuousOn hgsmooth.continuousOn
  obtain ⟨t, ht, hheight⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hh
    (show q ∈ Icc ((H.tube.height ∘ gamma) 0) ((H.tube.height ∘ gamma) 1) by
      simpa only [Function.comp_apply, hg0, hg1, mem_Icc] using And.intro hstart.le hend)
  have hsection : gamma t ∈ S := (H.tube.mem_sectionSet_iff hq (gamma t)).mpr hheight
  have hprefix := edistOf_le_metricPathELength g ht.1
    (hgsmooth.mono (Icc_subset_Icc le_rfl ht.2))
  have hlenprefix := metricPathELength_mono g gamma (a := 0) (b := t)
    (a' := 0) (b' := 1) le_rfl ht.2
  have hshort := (hprefix.trans hlenprefix).trans_lt hlength
  rw [hg0, H.edist_eq_ofReal_dist] at hshort
  have hreal : dist (H.axial.point s) (gamma t) < m / 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hshort
  have hlower : m ≤ dist (gamma t : UniformSpace.Completion W) H.endpoint := hmin hsection
  have hupper : dist (gamma t : UniformSpace.Completion W) H.endpoint < m := by
    calc
      _ ≤ dist (gamma t : UniformSpace.Completion W)
            (H.axial.point s : UniformSpace.Completion W) +
          dist (H.axial.point s : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
      _ = dist (H.axial.point s) (gamma t) + s := by
        rw [UniformSpace.Completion.dist_eq, H.axial.radial s hsL, dist_comm (gamma t)]
      _ < m := by linarith
  exact (not_lt_of_ge hlower) hupper

theorem finiteHorn_eventually_mem_subend (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) {w : ℕ → W}
    (hw : Tendsto (fun n => (w n : UniformSpace.Completion W)) atTop (𝓝 H.endpoint))
    (i : ℕ) : ∀ᶠ n in atTop, w n ∈ H.subend i := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H i
  have hnear := hw.eventually (Metric.ball_mem_nhds H.endpoint hdelta)
  exact hnear.mono (fun n hn => hball (w n) hn)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
