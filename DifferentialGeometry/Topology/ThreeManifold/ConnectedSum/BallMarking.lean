import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.PuncturedImageBall
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

theorem isPreconnected_compl_iUnion_of_collar {X : Type*} [TopologicalSpace X] [T1Space X]
    [PreconnectedSpace X] {ι : Type*} [Finite ι] (K V : ι → Set X)
    (hKcl : ∀ i, IsClosed (K i)) (hVop : ∀ i, IsOpen (V i)) (hKV : ∀ i, K i ⊆ V i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (K j))
    (hconn : ∀ i, IsConnected (V i \ K i)) :
    IsPreconnected ((⋃ i, K i)ᶜ : Set X) := by
  classical
  have hKcl' : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hKcl
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hsub (i : ι) : V i \ K i ⊆ (⋃ j, K j)ᶜ := by
    intro z hz
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro j hj
    by_cases hji : j = i
    · exact hz.2 (hji ▸ hj)
    · exact (Set.disjoint_left.mp (hdisj i j (fun hij => hji hij.symm)) hz.1) hj
  have hconst (i : ι) : ∃ c : Bool, ∀ z ∈ V i \ K i, f z = c := by
    obtain ⟨z0, hz0⟩ := (hconn i).nonempty
    exact ⟨f z0, fun z hz => (hconn i).isPreconnected.constant
      (hf.mono (hsub i)) hz hz0⟩
  choose c hc using hconst
  have hKdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j) := fun i j hij =>
    (hdisj i j hij).mono_left (hKV i)
  let g : X → Bool := fun z =>
    if hz : z ∈ ⋃ i, K i then c (Classical.choose (mem_iUnion.mp hz)) else f z
  have hgK : ∀ i, ∀ z ∈ K i, g z = c i := by
    intro i z hz
    have hzU : z ∈ ⋃ i, K i := mem_iUnion.mpr ⟨i, hz⟩
    have hspec : z ∈ K (Classical.choose (mem_iUnion.mp hzU)) :=
      Classical.choose_spec (mem_iUnion.mp hzU)
    have hidx : Classical.choose (mem_iUnion.mp hzU) = i := by
      by_contra hne
      exact (Set.disjoint_left.mp (hKdisj _ i hne) hspec) hz
    simp only [g, dif_pos hzU, hidx]
  have hgCompl : ∀ z, z ∉ ⋃ i, K i → g z = f z := by
    intro z hz
    simp only [g, dif_neg hz]
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ ⋃ i, K i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      refine (continuousAt_const (y := c i)).congr ?_
      filter_upwards [hVop i |>.mem_nhds (hKV i hi)] with w hw
      by_cases hwU : w ∈ ⋃ j, K j
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hwU
        by_cases hji : j = i
        · rw [hji] at hj
          rw [hgK i w hj]
        · exact absurd hj (Set.disjoint_left.mp (hdisj i j (fun hij => hji hij.symm)) hw)
      · rw [hgCompl w hwU]
        exact (hc i w ⟨hw, fun hwk => hwU (mem_iUnion.mpr ⟨i, hwk⟩)⟩).symm
    · refine ((hf z hz).continuousAt (hKcl'.isOpen_compl.mem_nhds hz)).congr ?_
      filter_upwards [hKcl'.isOpen_compl.mem_nhds hz] with w hw
      exact (hgCompl w hw).symm
  have hxy := IsPreconnected.constant isPreconnected_univ hgcont.continuousOn
    (mem_univ x) (mem_univ y)
  rw [hgCompl x hx, hgCompl y hy] at hxy
  exact hxy

theorem isConnected_shell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) :
    IsConnected (Metric.ball (0 : E) 2 \ Metric.closedBall (0 : E) 1) := by
  have hsphere : IsConnected (Metric.sphere (0 : E) 1) :=
    (isPathConnected_sphere hrank 0 zero_le_one).isConnected
  have hIoo : IsConnected (Set.Ioo (1 : ℝ) 2) := isConnected_Ioo (by norm_num)
  have heq : (fun p : E × ℝ => p.2 • p.1) '' (Metric.sphere (0 : E) 1 ×ˢ Set.Ioo (1 : ℝ) 2)
      = Metric.ball (0 : E) 2 \ Metric.closedBall (0 : E) 1 := by
    ext y
    constructor
    · rintro ⟨⟨v, t⟩, ⟨hv, ht⟩, rfl⟩
      have hv1 : ‖v‖ = 1 := by simpa [mem_sphere_iff_norm] using hv
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hv1, mul_one]
        exact ht.2
      · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hv1,
          mul_one]
        exact not_le.mpr ht.1
    · intro hy
      have hy1 : y ∈ Metric.ball (0 : E) 2 := hy.1
      have hy2 : y ∉ Metric.closedBall (0 : E) 1 := hy.2
      have hd1 : dist y 0 < 2 := Metric.mem_ball.mp hy1
      have hd2 : 1 < dist y 0 := by
        rw [Metric.mem_closedBall] at hy2
        exact not_le.mp hy2
      rw [dist_zero_right] at hd1 hd2
      have hpos : 0 < ‖y‖ := lt_trans zero_lt_one hd2
      refine ⟨(‖y‖⁻¹ • y, ‖y‖), ⟨?_, ⟨?_, hd1⟩⟩, ?_⟩
      · rw [mem_sphere_iff_norm]
        simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
          inv_mul_cancel₀ hpos.ne']
      · exact hd2
      · simp only [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [← heq]
  exact (hsphere.prod hIoo).image _ (by fun_prop)

structure BallMarking (M : ClosedOrientedManifold.{u} 3) (I : Type v) [Fintype I] where
  ball : I → OrientedBallChart M
  reserve_disjoint : ∀ i j, i ≠ j →
    Disjoint ((ball i).chart '' Metric.closedBall (0 : E₃) 2)
      ((ball j).chart '' Metric.closedBall (0 : E₃) 1)

namespace BallMarking

variable {M : ClosedOrientedManifold.{u} 3} {I : Type v} [Fintype I] (B : BallMarking M I)

abbrev reserve (i : I) : Set M.Carrier := (B.ball i).chart '' Metric.closedBall (0 : E₃) 2

abbrev collar (i : I) : Set M.Carrier := (B.ball i).chart '' Metric.ball (0 : E₃) 2

abbrev closedBallImage (i : I) : Set M.Carrier :=
  (B.ball i).chart '' Metric.closedBall (0 : E₃) 1

abbrev ballImage (i : I) : Set M.Carrier := (B.ball i).chart '' Metric.ball (0 : E₃) 1

abbrev sphereImage (i : I) : Set M.Carrier := (B.ball i).chart '' Metric.sphere (0 : E₃) 1

abbrev closedBallImages : Set M.Carrier := ⋃ i, B.closedBallImage i

abbrev ballImages : Set M.Carrier := ⋃ i, B.ballImage i

abbrev ambient : Set M.Carrier := B.closedBallImagesᶜ

abbrev Punctured : Type u := {x : M.Carrier // x ∉ B.ballImages}

theorem collar_subset_reserve (i : I) : B.collar i ⊆ B.reserve i :=
  Set.image_mono Metric.ball_subset_closedBall

theorem closedBallImage_subset_collar (i : I) : B.closedBallImage i ⊆ B.collar i :=
  Set.image_mono (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))

theorem closedBallImage_subset_reserve (i : I) : B.closedBallImage i ⊆ B.reserve i :=
  fun _ hx => B.collar_subset_reserve i (B.closedBallImage_subset_collar i hx)

theorem ballImage_subset_closedBallImage (i : I) : B.ballImage i ⊆ B.closedBallImage i :=
  Set.image_mono Metric.ball_subset_closedBall

theorem collar_disjoint_closedBallImage {i j : I} (hij : i ≠ j) :
    Disjoint (B.collar i) (B.closedBallImage j) :=
  (B.reserve_disjoint i j hij).mono_left (B.collar_subset_reserve i)

theorem disjoint_closedBallImage {i j : I} (hij : i ≠ j) :
    Disjoint (B.closedBallImage i) (B.closedBallImage j) :=
  (B.reserve_disjoint i j hij).mono_left (B.closedBallImage_subset_reserve i)

theorem isOpen_collar (i : I) : IsOpen (B.collar i) :=
  (B.ball i).chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball
    (fun _ hx => (B.ball i).closedBall_subset_source (Metric.ball_subset_closedBall hx))

theorem isCompact_closedBallImage (i : I) : IsCompact (B.closedBallImage i) :=
  (B.ball i).isCompact_closedBall_image

theorem isClosed_closedBallImage (i : I) : IsClosed (B.closedBallImage i) :=
  (B.isCompact_closedBallImage i).isClosed

theorem isConnected_collar_diff (i : I) :
    IsConnected (B.collar i \ B.closedBallImage i) := by
  have hrank : 1 < Module.rank ℝ E₃ := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  have hshell := isConnected_shell (E := E₃) hrank
  have hsub : Metric.ball (0 : E₃) 2 \ Metric.closedBall (0 : E₃) 1 ⊆
      (B.ball i).chart.source :=
    fun x hx => (B.ball i).closedBall_subset_source (Metric.ball_subset_closedBall hx.1)
  have hinj : Set.InjOn (B.ball i).chart (Metric.ball (0 : E₃) 2) :=
    fun x hx y hy h => (B.ball i).chart.toPartialEquiv.injOn
      ((B.ball i).closedBall_subset_source (Metric.ball_subset_closedBall hx))
      ((B.ball i).closedBall_subset_source (Metric.ball_subset_closedBall hy)) h
  have himg : (B.ball i).chart ''
        (Metric.ball (0 : E₃) 2 \ Metric.closedBall (0 : E₃) 1)
      = B.collar i \ B.closedBallImage i :=
    hinj.image_sdiff_subset (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
  rw [← himg]
  exact hshell.image _ ((B.ball i).chart.contMDiffOn_toFun.continuousOn.mono hsub)

theorem isPreconnected_ambient [ConnectedSpace M.Carrier] : IsPreconnected B.ambient := by
  have h := isPreconnected_compl_iUnion_of_collar (X := M.Carrier)
    (K := B.closedBallImage) (V := B.collar)
    (fun i => B.isClosed_closedBallImage i) (fun i => B.isOpen_collar i)
    (fun i => B.closedBallImage_subset_collar i)
    (fun i j hij => B.collar_disjoint_closedBallImage hij)
    (fun i => B.isConnected_collar_diff i)
  simpa only [BallMarking.ambient, BallMarking.closedBallImages] using h

theorem nonempty_ambient [ConnectedSpace M.Carrier] : B.ambient.Nonempty := by
  rcases isEmpty_or_nonempty I with hI | hI
  · refine ⟨Classical.arbitrary M.Carrier, ?_⟩
    rw [BallMarking.ambient, BallMarking.closedBallImages]
    simp only [compl_iUnion, mem_iInter, mem_compl_iff]
    exact fun i => isEmptyElim i
  · obtain ⟨i⟩ := hI
    obtain ⟨z, hz⟩ := (B.isConnected_collar_diff i).nonempty
    refine ⟨z, ?_⟩
    rw [BallMarking.ambient, BallMarking.closedBallImages, mem_compl_iff, mem_iUnion]
    rintro ⟨j, hj⟩
    by_cases hji : j = i
    · exact hz.2 (hji ▸ hj)
    · have hdisj := B.collar_disjoint_closedBallImage (i := i) (j := j)
        (fun hij => hji hij.symm)
      exact (Set.disjoint_left.mp hdisj hz.1) hj

theorem isPathConnected_ambient [ConnectedSpace M.Carrier] : IsPathConnected B.ambient := by
  have _ : LocallyPathConnectedSpace M.Carrier :=
    ChartedSpace.locallyPathConnectedSpace E₃ M.Carrier
  have hopen : IsOpen B.ambient :=
    (isClosed_iUnion_of_finite B.isClosed_closedBallImage).isOpen_compl
  exact hopen.isConnected_iff_isPathConnected.mp ⟨B.nonempty_ambient, B.isPreconnected_ambient⟩

theorem mem_reserve_of_norm_le (i : I) {w : E₃} (hw : ‖w‖ ≤ 2) :
    (B.ball i).chart w ∈ B.reserve i :=
  ⟨w, by simpa [mem_closedBall, dist_zero_right] using hw, rfl⟩

theorem chart_source_of_norm_le (i : I) {w : E₃} (hw : ‖w‖ ≤ 2) :
    w ∈ (B.ball i).chart.source :=
  (B.ball i).closedBall_subset_source (by simpa [mem_closedBall, dist_zero_right] using hw)

theorem notMem_closedBallImage_of_mem_reserve {i j : I} (hij : i ≠ j) {w : E₃}
    (hw : ‖w‖ ≤ 2) : (B.ball i).chart w ∉ B.closedBallImage j := fun h =>
  Set.disjoint_left.mp (B.reserve_disjoint i j hij) (B.mem_reserve_of_norm_le i hw) h

theorem notMem_ballImage_of_mem_reserve {i j : I} (hij : i ≠ j) {w : E₃} (hw : ‖w‖ ≤ 2) :
    (B.ball i).chart w ∉ B.ballImage j := fun h =>
  B.notMem_closedBallImage_of_mem_reserve hij hw (B.ballImage_subset_closedBallImage j h)

theorem notMem_ballImage_self (i : I) {w : E₃} (hw : 1 ≤ ‖w‖)
    (hws : w ∈ (B.ball i).chart.source) : (B.ball i).chart w ∉ B.ballImage i := by
  rintro ⟨z, hz, hz'⟩
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
  have hzs : z ∈ (B.ball i).chart.source :=
    B.chart_source_of_norm_le i (le_trans (le_of_lt hz1) (by norm_num : (1 : ℝ) ≤ 2))
  have hzw : z = w := (B.ball i).chart.toPartialEquiv.injOn hzs hws hz'
  rw [hzw] at hz1
  exact not_lt_of_ge hw hz1

theorem ambient_subset_ballImages_compl : B.ambient ⊆ B.ballImagesᶜ := by
  intro z hz
  rw [BallMarking.ambient, BallMarking.closedBallImages, mem_compl_iff, mem_iUnion] at hz
  rw [BallMarking.ballImages, mem_compl_iff, mem_iUnion]
  rintro ⟨j, hj⟩
  exact hz ⟨j, B.ballImage_subset_closedBallImage j hj⟩

theorem continuousOn_radial (i : I) {v : E₃} (hv : ‖v‖ = 1) :
    ContinuousOn (fun t : ℝ => (B.ball i).chart ((1 + t) • v)) (Set.Icc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun t : ℝ => (1 + t) • v) (Set.Icc (0 : ℝ) 1) := by fun_prop
  have h2 : MapsTo (fun t : ℝ => (1 + t) • v) (Set.Icc (0 : ℝ) 1)
      (B.ball i).chart.source := by
    intro t ht
    refine B.chart_source_of_norm_le i ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), hv, mul_one]
    linarith [ht.2]
  exact (B.ball i).chart.contMDiffOn_toFun.continuousOn.comp' h1 h2

theorem joinedIn_radial (i : I) {v : E₃} (hv : v ∈ Metric.sphere (0 : E₃) 1) :
    JoinedIn B.ballImagesᶜ ((B.ball i).chart v) ((B.ball i).chart ((2 : ℝ) • v)) := by
  have hvn : ‖v‖ = 1 := by simpa [mem_sphere_iff_norm] using hv
  have hnorm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖(1 + t) • v‖ = 1 + t := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), hvn, mul_one]
  refine JoinedIn.ofLine (f := fun t : ℝ => (B.ball i).chart ((1 + t) • v))
    (B.continuousOn_radial i hvn) ?_ ?_ ?_
  · simp
  · rw [one_add_one_eq_two]
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [BallMarking.ballImages, mem_compl_iff, mem_iUnion]
    rintro ⟨j, hj⟩
    by_cases hji : j = i
    · rw [hji] at hj
      have hy1 : 1 ≤ ‖(1 + t) • v‖ := by rw [hnorm t ht]; linarith [ht.1]
      have hsrc : (1 + t) • v ∈ (B.ball i).chart.source :=
        B.chart_source_of_norm_le i (by rw [hnorm t ht]; linarith [ht.2])
      exact B.notMem_ballImage_self i hy1 hsrc hj
    · have hle : ‖(1 + t) • v‖ ≤ 2 := by rw [hnorm t ht]; linarith [ht.2]
      exact B.notMem_ballImage_of_mem_reserve (fun hij => hji hij.symm) hle hj

theorem isPathConnected_ballImages_compl [ConnectedSpace M.Carrier] :
    IsPathConnected B.ballImagesᶜ := by
  obtain ⟨x₀, hx₀, hjoin⟩ := B.isPathConnected_ambient
  refine ⟨x₀, B.ambient_subset_ballImages_compl hx₀, ?_⟩
  intro y hy
  by_cases hyamb : y ∈ B.ambient
  · exact (hjoin hyamb).mono B.ambient_subset_ballImages_compl
  · have hyc : y ∈ B.closedBallImages := by
      simpa only [BallMarking.ambient, mem_compl_iff, not_not] using hyamb
    rw [BallMarking.closedBallImages, mem_iUnion] at hyc
    obtain ⟨i, hi⟩ := hyc
    obtain ⟨w, hw, rfl⟩ := hi
    have hwle : ‖w‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hw
    have hy' : ¬ ∃ k, (B.ball i).chart w ∈ B.ballImage k := by
      simpa only [BallMarking.ballImages, mem_compl_iff, mem_iUnion] using hy
    have hwge : 1 ≤ ‖w‖ := by
      by_contra hlt
      exact hy' ⟨i, ⟨w, by simpa [mem_ball, dist_zero_right] using not_le.mp hlt, rfl⟩⟩
    have hwn : ‖w‖ = 1 := le_antisymm hwle hwge
    have hwamb : (B.ball i).chart ((2 : ℝ) • w) ∈ B.ambient := by
      rw [BallMarking.ambient, BallMarking.closedBallImages, mem_compl_iff, mem_iUnion]
      rintro ⟨j, hj⟩
      by_cases hji : j = i
      · rw [hji] at hj
        obtain ⟨z, hz, hz'⟩ := hj
        have hz1 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
        have hzs : z ∈ (B.ball i).chart.source :=
          B.chart_source_of_norm_le i (le_trans hz1 (by norm_num : (1 : ℝ) ≤ 2))
        have hws : (2 : ℝ) • w ∈ (B.ball i).chart.source :=
          B.chart_source_of_norm_le i (by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hwn,
              mul_one])
        have hzw : z = (2 : ℝ) • w := (B.ball i).chart.toPartialEquiv.injOn hzs hws hz'
        rw [hzw, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hwn,
          mul_one] at hz1
        norm_num at hz1
      · have hle : ‖(2 : ℝ) • w‖ ≤ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hwn, mul_one]
        exact B.notMem_closedBallImage_of_mem_reserve (fun hij => hji hij.symm) hle hj
    exact ((hjoin hwamb).mono B.ambient_subset_ballImages_compl).trans
      (B.joinedIn_radial i (by simpa [mem_sphere_iff_norm] using hwn)).symm

theorem closedBallImage_nonempty (i : I) : (B.closedBallImage i).Nonempty :=
  ⟨(B.ball i).chart 0, ⟨0, mem_closedBall_self (by norm_num), rfl⟩⟩

def empty : BallMarking M PEmpty where
  ball := PEmpty.elim
  reserve_disjoint := fun i => PEmpty.elim i

def singleton (c : OrientedBallChart M) : BallMarking M PUnit where
  ball := fun _ => c
  reserve_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

def pair (c : OrientedBallChart M) : BallMarking M Bool :=
  let hd := exists_disjointOrientedBallChart_closedBall c
  let d : OrientedBallChart M := Classical.choose hd
  let he := Classical.choose_spec hd
  let e : OrientedBallChart M := Classical.choose he
  let hspec := Classical.choose_spec he
  { ball := fun k => if k then e else d
    reserve_disjoint := by
      have h₁ := hspec.1
      have h₂ := hspec.2
      intro i j hij
      cases i <;> cases j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact absurd rfl hij
      · exact Set.disjoint_left.mpr fun x hx => by
          obtain ⟨u, hu, rfl⟩ := hx
          exact h₁ u hu
      · exact Set.disjoint_left.mpr fun x hx => by
          obtain ⟨u, hu, rfl⟩ := hx
          exact h₂ u hu
      · exact absurd rfl hij }

end BallMarking

end DifferentialGeometry.Topology
