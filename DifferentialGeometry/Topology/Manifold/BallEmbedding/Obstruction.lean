import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallEmbeddingIsotopy

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
  [IsManifold ThreeModel ∞ U] {o : ManifoldOrientation ThreeModel U 3}

theorem not_supportedBallEmbeddingIsotopy_swap {ι : Type u} [DecidableEq ι]
    (e : ι → OrientedBallEmbedding U o) (i j : ι) (hij : i ≠ j)
    (hne : (e i).chart (0 : ThreeSpace) ≠ (e j).chart (0 : ThreeSpace)) :
    ¬ SupportedBallEmbeddingIsotopy ι U o e
      (fun k => if k = i then e j else if k = j then e i else e k) := by
  rintro ⟨J, V, r, -, -, -, -, -, hVfix, hr, -, hJ1, havoid⟩
  have hmem : (0 : ThreeSpace) ∈ Metric.closedBall (0 : ThreeSpace) r :=
    Metric.mem_closedBall_self hr.le
  have havoid' : (e i).chart (0 : ThreeSpace) ∉ V j := havoid i j hij (0 : ThreeSpace) hmem
  have hfix : J j 1 ((e i).chart (0 : ThreeSpace)) = (e i).chart (0 : ThreeSpace) :=
    hVfix j 1 havoid'
  have hJ1' : J j 1 ((e j).chart (0 : ThreeSpace)) = (e i).chart (0 : ThreeSpace) := by
    have h := hJ1 j (0 : ThreeSpace) hmem
    simpa [hij.symm] using h
  have hEq : J j 1 ((e j).chart (0 : ThreeSpace)) = J j 1 ((e i).chart (0 : ThreeSpace)) := by
    rw [hJ1', hfix]
  have hval : (e j).chart (0 : ThreeSpace) = (e i).chart (0 : ThreeSpace) := by
    have h := congrArg (fun x : U => (J j 1).symm x) hEq
    simpa using h
  exact hne hval.symm

theorem disjoint_chart_image_closedBall_affine
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M)
    (s : ThreeSpace) (r : ℝ) (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) (hbig : 1 + r < ‖s‖) :
    Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      ((c.affine s r hr hs).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
  have hx1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hx'1 : ‖x'‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx'
  have hxs : x ∈ c.chart.source :=
    c.closedBall_subset_source (by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith)
  have hsx's : s + r • x' ∈ c.chart.source :=
    c.closedBall_subset_source (by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖s + r • x'‖ ≤ ‖s‖ + ‖r • x'‖ := norm_add_le _ _
        _ = ‖s‖ + r * ‖x'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        _ ≤ ‖s‖ + r * 1 := by nlinarith [norm_nonneg s]
        _ ≤ 2 := by nlinarith)
  have hkey : (c.affine s r hr hs).chart x' = c.chart (s + r • x') :=
    DifferentialGeometry.Topology.OrientedBallChart.affine_apply c s r hr hs x'
  have hinj : x = s + r • x' :=
    c.chart.toPartialEquiv.injOn hxs hsx's (hxx'.symm.trans hkey)
  have hsub : x - r • x' = s := by rw [hinj]; simp
  have hnorm : ‖s‖ = ‖x - r • x'‖ := by rw [hsub]
  have hle : ‖x - r • x'‖ ≤ 1 + r := by
    calc ‖x - r • x'‖ ≤ ‖x‖ + ‖r • x'‖ := norm_sub_le _ _
      _ = ‖x‖ + r * ‖x'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ 1 + r * 1 := by nlinarith [norm_nonneg x, norm_nonneg x']
      _ = 1 + r := by ring
  have : ‖s‖ ≤ 1 + r := by rw [hnorm]; exact hle
  linarith

theorem not_supportedBallEmbeddingIsotopy_standardThreeSphere :
    ∃ (e e' : Fin 2 → OrientedBallEmbedding
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).orientation),
      (Pairwise fun i j => Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) ∧
      (Pairwise fun i j => Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) ∧
      ¬ SupportedBallEmbeddingIsotopy (Fin 2)
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).orientation e e' := by
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{0} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{0}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{0}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hs : ‖s‖ + 2 * (1 / 8 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have hbig : 1 + (1 / 8 : ℝ) < ‖s‖ := by rw [hnorm]; norm_num
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 : ‖s‖ = 0 := by rw [h0, norm_zero]
    rw [hnorm] at h1
    norm_num at h1
  let d : DifferentialGeometry.Topology.OrientedBallChart M :=
    c.affine s (1 / 8) (by norm_num) hs
  have hdisj : Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      (d.chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    disjoint_chart_image_closedBall_affine c s (1 / 8) (by norm_num) hs hbig
  have hne : d.chart (0 : ThreeSpace) ≠ c.chart (0 : ThreeSpace) :=
    DifferentialGeometry.Topology.affine_chart_zero_ne c s (1 / 8)
      (by norm_num) hs hs0
  let e : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d
  let e' : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart d
      else OrientedBallEmbedding.ofOrientedBallChart c
  have h0 : e 0 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [e]
  have h1 : e 1 = OrientedBallEmbedding.ofOrientedBallChart d := by simp [e]
  have h1' : e' 1 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [e']
  have h0' : e' 0 = OrientedBallEmbedding.ofOrientedBallChart d := by simp [e']
  have hchartc : (OrientedBallEmbedding.ofOrientedBallChart c).chart = c.chart := rfl
  have hchartd : (OrientedBallEmbedding.ofOrientedBallChart d).chart = d.chart := rfl
  have hswap : (fun k : Fin 2 =>
      if k = 0 then e 1 else if k = 1 then e 0 else e k) = e' := by
    funext k
    fin_cases k <;> simp [h0, h1, h0', h1']
  have hdisj_e : Pairwise fun i j : Fin 2 =>
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [h0, h1, hchartc, hchartd] using hdisj
    · simpa [h0, h1, hchartc, hchartd] using hdisj.symm
    · exact absurd rfl hij
  have hdisj_e' : Pairwise fun i j : Fin 2 =>
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [h0', h1', hchartc, hchartd] using hdisj.symm
    · simpa [h0', h1', hchartc, hchartd] using hdisj
    · exact absurd rfl hij
  refine ⟨e, e', ?_, ?_, ?_⟩
  · exact hdisj_e
  · exact hdisj_e'
  · rw [← hswap]
    refine not_supportedBallEmbeddingIsotopy_swap e 0 1 (by decide) ?_
    simpa [h0, h1, hchartc, hchartd] using hne.symm

theorem not_forall_supportedBallEmbeddingIsotopy :
    ¬ (∀ (ι : Type) [Fintype ι] (U : Type) [TopologicalSpace U]
        [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
        (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o),
        SupportedBallEmbeddingIsotopy ι U o e e') := by
  rintro h
  obtain ⟨e, e', -, -, hbad⟩ := not_supportedBallEmbeddingIsotopy_standardThreeSphere
  exact hbad (h (Fin 2) _ _ e e')

theorem not_forall_supportedBallEmbeddingIsotopy_universal :
    ¬ (∀ (ι : Type u) [Fintype ι] (U : Type u) [TopologicalSpace U]
        [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
        (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o),
        SupportedBallEmbeddingIsotopy ι U o e e') := by
  rintro h
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{u}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hs : ‖s‖ + 2 * (1 / 8 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have hbig : 1 + (1 / 8 : ℝ) < ‖s‖ := by rw [hnorm]; norm_num
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 : ‖s‖ = 0 := by rw [h0, norm_zero]
    rw [hnorm] at h1
    norm_num at h1
  let d : DifferentialGeometry.Topology.OrientedBallChart M :=
    c.affine s (1 / 8) (by norm_num) hs
  have hne : d.chart (0 : ThreeSpace) ≠ c.chart (0 : ThreeSpace) :=
    DifferentialGeometry.Topology.affine_chart_zero_ne c s (1 / 8) (by norm_num) hs hs0
  let e : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i.down = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d
  let e' : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i.down = 0 then OrientedBallEmbedding.ofOrientedBallChart d
      else OrientedBallEmbedding.ofOrientedBallChart c
  have hswap : (fun k : ULift.{u, 0} (Fin 2) => if k = ULift.up 0 then e (ULift.up 1)
      else if k = ULift.up 1 then e (ULift.up 0) else e k) = e' := by
    funext k
    obtain ⟨n⟩ := k
    fin_cases n <;> simp [e, e']
  have hfrontier := h (ULift.{u, 0} (Fin 2)) M.Carrier M.orientation e e'
  rw [← hswap] at hfrontier
  refine not_supportedBallEmbeddingIsotopy_swap e (ULift.up 0) (ULift.up 1) (by simp) ?_ hfrontier
  have h0 : e (ULift.up 0) = OrientedBallEmbedding.ofOrientedBallChart c := by simp [e]
  have h1 : e (ULift.up 1) = OrientedBallEmbedding.ofOrientedBallChart d := by simp [e]
  have hchartc : (OrientedBallEmbedding.ofOrientedBallChart c).chart = c.chart := rfl
  have hchartd : (OrientedBallEmbedding.ofOrientedBallChart d).chart = d.chart := rfl
  simpa [h0, h1, hchartc, hchartd] using hne.symm

theorem exists_disjoint_ballEmbedding_family_not_eqOn_closedBall :
    ∃ (e e' : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding
        DifferentialGeometry.Topology.standardThreeSphereLift.{u}.Carrier
        DifferentialGeometry.Topology.standardThreeSphereLift.{u}.orientation),
      (Pairwise fun i j =>
        Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
          ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) ∧
      (Pairwise fun i j =>
        Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
          ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) ∧
      ¬ ∃ F : DifferentialGeometry.Topology.standardThreeSphereLift.{u}.Carrier →
          DifferentialGeometry.Topology.standardThreeSphereLift.{u}.Carrier,
        ∀ i x, x ∈ Metric.closedBall (0 : ThreeSpace) 2 →
          F ((e i).chart x) = (e' i).chart x := by
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{u}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  set s' : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) with hs'def
  set z : ThreeSpace := (7 / 5 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hzdef
  set x : ThreeSpace := (-(2 / 5) : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hxdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hnorm' : ‖s'‖ = 3 / 2 := by
    rw [hs'def, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hznorm : ‖z‖ = 7 / 5 := by
    rw [hzdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 5)]
    simp
  have hxnorm : ‖x‖ = 2 / 5 := by
    rw [hxdef, norm_smul]
    simp
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hs : ‖s‖ + 2 * (1 / 4 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have hs' : ‖s'‖ + 2 * (1 / 4 : ℝ) ≤ 2 := by rw [hnorm']; norm_num
  have hbig : 1 + (1 / 4 : ℝ) < ‖s‖ := by rw [hnorm]; norm_num
  have hbig' : 1 + (1 / 4 : ℝ) < ‖s'‖ := by rw [hnorm']; norm_num
  let d : DifferentialGeometry.Topology.OrientedBallChart M := c.affine s (1 / 4) hr hs
  let d' : DifferentialGeometry.Topology.OrientedBallChart M := c.affine s' (1 / 4) hr hs'
  let eFin : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d
  let eFin' : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d'
  let e : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => eFin i.down
  let e' : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => eFin' i.down
  have hchartc : (OrientedBallEmbedding.ofOrientedBallChart c).chart = c.chart := rfl
  have hchartd : (OrientedBallEmbedding.ofOrientedBallChart d).chart = d.chart := rfl
  have hchartd' : (OrientedBallEmbedding.ofOrientedBallChart d').chart = d'.chart := rfl
  have hdisjc : Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      (d.chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    disjoint_chart_image_closedBall_affine c s (1 / 4) hr hs hbig
  have hdisjc' : Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      (d'.chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    disjoint_chart_image_closedBall_affine c s' (1 / 4) hr hs' hbig'
  have he0 : eFin 0 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [eFin]
  have he1 : eFin 1 = OrientedBallEmbedding.ofOrientedBallChart d := by simp [eFin]
  have he0' : eFin' 0 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [eFin']
  have he1' : eFin' 1 = OrientedBallEmbedding.ofOrientedBallChart d' := by simp [eFin']
  have hdisjFin : Pairwise fun i j : Fin 2 =>
      Disjoint ((eFin i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((eFin j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [he0, he1, hchartc, hchartd] using hdisjc
    · simpa [he0, he1, hchartc, hchartd] using hdisjc.symm
    · exact absurd rfl hij
  have hdisjFin' : Pairwise fun i j : Fin 2 =>
      Disjoint ((eFin' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((eFin' j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [he0', he1', hchartc, hchartd'] using hdisjc'
    · simpa [he0', he1', hchartc, hchartd'] using hdisjc'.symm
    · exact absurd rfl hij
  have hdisj : Pairwise fun i j : ULift.{u, 0} (Fin 2) =>
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    fun i j hij => hdisjFin (i := i.down) (j := j.down) fun hd => hij (ULift.down_injective hd)
  have hdisj' : Pairwise fun i j : ULift.{u, 0} (Fin 2) =>
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    fun i j hij => hdisjFin' (i := i.down) (j := j.down) fun hd => hij (ULift.down_injective hd)
  refine ⟨e, e', hdisj, hdisj', ?_⟩
  rintro ⟨F, hball⟩
  have he1e : e (ULift.up 1) = OrientedBallEmbedding.ofOrientedBallChart d := by
    simp [e, eFin]
  have he0e : e (ULift.up 0) = OrientedBallEmbedding.ofOrientedBallChart c := by
    simp [e, eFin]
  have he1'e : e' (ULift.up 1) = OrientedBallEmbedding.ofOrientedBallChart d' := by
    simp [e', eFin']
  have he0'e : e' (ULift.up 0) = OrientedBallEmbedding.ofOrientedBallChart c := by
    simp [e', eFin']
  have hz2 : z ∈ Metric.closedBall (0 : ThreeSpace) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, hznorm]
    norm_num
  have hx2 : x ∈ Metric.closedBall (0 : ThreeSpace) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, hxnorm]
    norm_num
  have hvec : s + (1 / 4 : ℝ) • x = z := by
    rw [hsdef, hxdef, hzdef]
    simp only [smul_smul, ← add_smul]
    norm_num
  have hsame : (e (ULift.up 1)).chart x = (e (ULift.up 0)).chart z := by
    rw [he1e, he0e, hchartd, hchartc,
      DifferentialGeometry.Topology.OrientedBallChart.affine_apply c s (1 / 4) hr hs x, hvec]
  have hEq : (e' (ULift.up 1)).chart x = (e' (ULift.up 0)).chart z := by
    have h1 := hball (ULift.up 1) x hx2
    have h0 := hball (ULift.up 0) z hz2
    rw [hsame] at h1
    exact h1.symm.trans h0
  have hsrc : s' + (1 / 4 : ℝ) • x ∈ c.chart.source := by
    apply c.closedBall_subset_source
    rw [Metric.mem_closedBall, dist_zero_right]
    have hquarter : ‖(1 / 4 : ℝ) • x‖ = (1 / 4) * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc ‖s' + (1 / 4 : ℝ) • x‖ ≤ ‖s'‖ + ‖(1 / 4 : ℝ) • x‖ := norm_add_le _ _
      _ = ‖s'‖ + (1 / 4) * ‖x‖ := by rw [hquarter]
      _ ≤ 3 / 2 + (1 / 4) * (2 / 5) := by rw [hnorm', hxnorm]
      _ ≤ 2 := by norm_num
  have hsrc0 : z ∈ c.chart.source := by
    apply c.closedBall_subset_source
    rw [Metric.mem_closedBall, dist_zero_right, hznorm]
    norm_num
  rw [he1'e, he0'e, hchartd', hchartc,
    DifferentialGeometry.Topology.OrientedBallChart.affine_apply c s' (1 / 4) hr hs' x] at hEq
  have hvec' : s' + (1 / 4 : ℝ) • x = z :=
    c.chart.toPartialEquiv.injOn hsrc hsrc0 hEq
  have hne : s' + (1 / 4 : ℝ) • x ≠ z := by
    intro hcontra
    have hc := congrArg (fun y : ThreeSpace => y 1) hcontra
    rw [hs'def, hxdef, hzdef] at hc
    simp at hc
  exact hne hvec'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
