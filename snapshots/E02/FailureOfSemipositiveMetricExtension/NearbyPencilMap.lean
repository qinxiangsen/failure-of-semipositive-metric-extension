import FailureOfSemipositiveMetricExtension.GlobalPencilGeneration
import FailureOfSemipositiveMetricExtension.ProjectiveLineMaps
import FailureOfSemipositiveMetricExtension.ProjectiveLineBundle

/-! The actual generated pencil defines a global complex analytic map from every
noncentral surface fibre to the actual projective line. Local coefficient vectors
are compared by their proved bundle transition, so no global continuous choice of
bundle frame or homogeneous representative is used. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveLine
noncomputable section
open Set

theorem vectorPoint_smul (a : ℂ) (ha : a ≠ 0) (v : Blowup.Plane) :
    vectorPoint (a • v) = vectorPoint v := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [vectorPoint_eq_mk _ (smul_ne_zero ha hv),vectorPoint_eq_mk _ hv]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a,rfl⟩

theorem vectorPoint_mem_chartSet_iff (i : Fin 2) (v : Blowup.Plane) (hv : v ≠ 0) :
    vectorPoint v ∈ chartSet i ↔ v i ≠ 0 := by
  fin_cases i
  · constructor
    · intro hp h0
      have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext j
        fin_cases j <;> assumption
      rw [vectorPoint_eq_param_one v h1] at hp
      have hn : v 0 / v 1 ≠ 0 := (param_mem_chartSet_iff 1 0 _).mp hp
      exact hn (by change v 0 = 0 at h0; rw [h0,zero_div])
    · intro h0
      rw [vectorPoint_eq_param_zero v h0]
      exact ⟨_,rfl⟩
  · constructor
    · intro hp h1
      have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        ext j
        fin_cases j <;> assumption
      rw [vectorPoint_eq_param_zero v h0] at hp
      have hn : v 1 / v 0 ≠ 0 := (param_mem_chartSet_iff 0 1 _).mp hp
      exact hn (by change v 1 = 0 at h1; rw [h1,zero_div])
    · intro h1
      rw [vectorPoint_eq_param_one v h1]
      exact ⟨_,rfl⟩

/-- O(1) coefficient transitions are the quotient of homogeneous coordinates in
source-to-target order. -/
theorem bundle_ratio_vectorPoint (i j : Fin 2) (v : Blowup.Plane)
    (hi : v i ≠ 0) (hj : v j ≠ 0) :
    ProjectiveLineBundle.ratio i j (vectorPoint v) = v i / v j := by
  fin_cases i <;> fin_cases j
  · change 1 = v 0 / v 0
    exact (div_self hi).symm
  · change coordinates 1 (vectorPoint v) = v 0 / v 1
    rw [vectorPoint_eq_param_one v hj,coordinates_param]
  · change coordinates 0 (vectorPoint v) = v 1 / v 0
    rw [vectorPoint_eq_param_zero v hj,coordinates_param]
  · change 1 = v 1 / v 1
    exact (div_self hi).symm

end
end FailureOfSemipositiveMetricExtension.ProjectiveLine

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
noncomputable section
open Set Bundle IsManifold Topology
open FixedFiberBundle
open scoped Manifold ContDiff

abbrev lineCore (t : ℂ) := core t (-2) (fun _ => 1)
abbrev pencilSection (t : ℂ) (k : Fin 2) := GlobalLineBundle.fibrePencil t k

def valueVector (t : ℂ) (p : Fiber t) : Blowup.Plane :=
  fun k => (show ℂ from sectionValue (pencilSection t k) p)

def localVector (t : ℂ) (i : Index) (p : Fiber t) : Blowup.Plane :=
  fun k => (pencilSection t k).coefficient i p

theorem valueVector_ne_zero (t : ℂ) (ht : t ≠ 0) (p : Fiber t) : valueVector t p ≠ 0 := by
  obtain ⟨k,hk⟩ := GlobalLineBundle.fibrePencil_no_basepoint t ht p
  exact fun hz => hk (congrFun hz k)

theorem localVector_ne_zero (t : ℂ) (ht : t ≠ 0) (i : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i) : localVector t i p ≠ 0 := by
  obtain ⟨k,hk⟩ := GlobalLineBundle.fibrePencil_no_basepoint t ht p
  exact fun hz => hk ((sectionValue_zero_iff (pencilSection t k) i p hp).mpr (congrFun hz k))

theorem localVector_change (t : ℂ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) :
    localVector t j p = gain t (-2) (fun _ => 1) i j p • localVector t i p := by
  ext k
  exact ((pencilSection t k).compatible i j p hp).symm

theorem lineGain_ne_zero (t : ℂ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) : gain t (-2) (fun _ => 1) i j p ≠ 0 := by
  have h := gain_comp t (-2) (fun _ => 1) i j i p ⟨hp,hp.1⟩
  exact right_ne_zero_of_mul_eq_one (h.trans (gain_self t (-2) (fun _ => 1) i p))

/-- The global projective map of the two actual pencil sections. -/
def pencilMap (t : ℂ) (p : Fiber t) : ProjectiveLine.Point :=
  ProjectiveLine.vectorPoint (valueVector t p)

/-- Any genuine local frame gives the same projective point. -/
theorem pencilMap_local (t : ℂ) (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    pencilMap t p = ProjectiveLine.vectorPoint (localVector t i p) := by
  let j := (lineCore t).indexAt p
  have hj : p ∈ baseSet t j := (lineCore t).mem_baseSet_at p
  have h := congrArg ProjectiveLine.vectorPoint (localVector_change t j i p ⟨hj,hp⟩)
  rw [ProjectiveLine.vectorPoint_smul _ (lineGain_ne_zero t j i p ⟨hj,hp⟩)] at h
  exact h.symm

theorem localVector_contMDiffOn (t : ℂ) (i : Index) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,Blowup.Plane) ω (localVector t i) (baseSet t i) :=
  contMDiffOn_pi_space.mpr (fun k => (pencilSection t k).analytic i)

/-- Analyticity includes all exceptional points, using the proved no-basepoint theorem. -/
theorem pencilMap_contMDiff (t : ℂ) (ht : t ≠ 0) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (pencilMap t) := by
  intro p
  let i := (lineCore t).indexAt p
  have hp : p ∈ baseSet t i := (lineCore t).mem_baseSet_at p
  have h := (ProjectiveLine.vectorPoint_contMDiffAt ω (localVector t i p)
    (localVector_ne_zero t ht i p hp)).comp p
      ((localVector_contMDiffOn t i).contMDiffAt ((baseSet_isOpen t i).mem_nhds hp))
  apply h.congr_of_eventuallyEq
  filter_upwards [(baseSet_isOpen t i).mem_nhds hp] with q hq
  exact pencilMap_local t i q hq

theorem pencilMap_continuous (t : ℂ) (ht : t ≠ 0) : Continuous (pencilMap t) :=
  (pencilMap_contMDiff t ht).continuous

theorem pencilMap_chartSet_iff (t : ℂ) (ht : t ≠ 0) (i : Index) (k : Fin 2)
    (p : Fiber t) (hp : p ∈ baseSet t i) :
    pencilMap t p ∈ ProjectiveLine.chartSet k ↔ (pencilSection t k).coefficient i p ≠ 0 := by
  rw [pencilMap_local t i p hp]
  exact ProjectiveLine.vectorPoint_mem_chartSet_iff k _ (localVector_ne_zero t ht i p hp)

theorem pencilMap_ratio (t : ℂ) (i : Index) (k l : Fin 2) (p : Fiber t)
    (hp : p ∈ baseSet t i) (hk : (pencilSection t k).coefficient i p ≠ 0)
    (hl : (pencilSection t l).coefficient i p ≠ 0) :
    ProjectiveLineBundle.ratio k l (pencilMap t p) =
      (pencilSection t k).coefficient i p / (pencilSection t l).coefficient i p := by
  rw [pencilMap_local t i p hp]
  exact ProjectiveLine.bundle_ratio_vectorPoint k l _ hk hl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
