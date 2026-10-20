import FailureOfSemipositiveMetricExtension.HisamotoLineBundle

/-! The exceptional curve is the actual centre fibre. Its local defining
functions form a regular section of bidegree `(1,-1)`, proving the geometric
identification `E = H - R` at the level of actual analytic bundle frames. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set
open scoped Manifold ContDiff

def centre : PlanePoint := ProjectivePlane.param 0 (0,0)
def exceptionalSet : Set Point := {q | blowdown q = centre}

@[simp] theorem centrePair_component (v : Fin 3 → ℂ) (i : Fin 2) :
    centrePair v i = v (planeIndex i 1) := by
  fin_cases i <;> simp [centrePair,planeIndex]

/-- Coefficient of the canonical exceptional section in a genuine ambient frame. -/
def exceptionalCoefficient (f : Frame) (q : Point) : ℂ :=
  ProjectivePlane.vector (planeIndex f.1 f.2)
    (ProjectivePlane.coordinates (planeIndex f.1 f.2) (blowdown q)) (planeIndex f.1 1)

theorem exceptionalCoefficient_incidence (f : Frame) (q : Point) (hq : q ∈ LineBundle.baseSet f) :
    centrePair (ProjectivePlane.vector (planeIndex f.1 f.2)
      (ProjectivePlane.coordinates (planeIndex f.1 f.2) (blowdown q))) =
    exceptionalCoefficient f q • directionVector f.1 (ProjectiveLine.coordinates f.1 (ruling q)) := by
  have hp := planeChart_of_affineChart f.1 f.2 q hq
  have hd := ((mem_affineChart_source f.1 f.2 q).mp hq).1
  have h : Incidence
      (ProjectivePlane.param (planeIndex f.1 f.2) (ProjectivePlane.coordinates (planeIndex f.1 f.2) (blowdown q)))
      (ProjectiveLine.param f.1 (ProjectiveLine.coordinates f.1 (ruling q))) := by
    rw [ProjectivePlane.param_coordinates _ _ hp,ProjectiveLine.param_coordinates _ _ hd]
    exact q.property
  rw [ProjectivePlane.param,incidence_mk_iff,← directionVector_mk,
    Projectivization.submodule_mk,Submodule.mem_span_singleton] at h
  obtain ⟨a,ha⟩ := h
  have he : a = exceptionalCoefficient f q := by
    simpa only [Pi.smul_apply,smul_eq_mul,directionVector_self,mul_one,centrePair_component]
      using congrFun ha f.1
  rw [he] at ha
  exact ha.symm

theorem plane_normalization_scale (a c : Fin 3) (p : PlanePoint)
    (ha : p ∈ ProjectivePlane.chartSet a) (hc : p ∈ ProjectivePlane.chartSet c) :
    ProjectivePlaneBundle.ratio a c p • ProjectivePlane.vector a (ProjectivePlane.coordinates a p) =
      ProjectivePlane.vector c (ProjectivePlane.coordinates c p) := by
  have h := ProjectivePlane.vector_transition c a (ProjectivePlane.coordinates c p)
    (ProjectivePlaneBundle.coordinates_mem_overlap a c p ha hc)
  have he : ProjectivePlane.transition c a (ProjectivePlane.coordinates c p) = ProjectivePlane.coordinates a p := by
    rw [← ProjectivePlane.coordinates_transition c a (ProjectivePlane.coordinates c p)
      (ProjectivePlaneBundle.coordinates_mem_overlap a c p ha hc),ProjectivePlane.param_coordinates c p hc]
  rwa [he] at h

theorem line_ratio_eq_vector (i j : Fin 2) (p : Direction) :
    ProjectiveLineBundle.ratio i j p = directionVector j (ProjectiveLine.coordinates j p) i := by
  fin_cases i <;> fin_cases j <;>
    simp [ProjectiveLineBundle.ratio,directionVector,Blowup.vectorX,Blowup.vectorY]

theorem direction_normalization_scale (i j : Fin 2) (p : Direction)
    (hi : p ∈ ProjectiveLine.chartSet i) (hj : p ∈ ProjectiveLine.chartSet j) :
    ProjectiveLineBundle.ratio i j p • directionVector i (ProjectiveLine.coordinates i p) =
      directionVector j (ProjectiveLine.coordinates j p) := by
  have he : Projectivization.mk ℂ (directionVector j (ProjectiveLine.coordinates j p))
      (directionVector_ne_zero _ _) =
      Projectivization.mk ℂ (directionVector i (ProjectiveLine.coordinates i p))
      (directionVector_ne_zero _ _) := by
    simp only [directionVector_mk,ProjectiveLine.param_coordinates i p hi,ProjectiveLine.param_coordinates j p hj]
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
  have hc : a = ProjectiveLineBundle.ratio i j p := by
    rw [line_ratio_eq_vector]
    simpa only [Pi.smul_apply,smul_eq_mul,directionVector_self,mul_one] using congrFun ha i
  rwa [hc] at ha

/-- Exact section compatibility in the actual bidegree `(1,-1)` bundle. -/
theorem exceptionalCoefficient_compatible (f g : Frame) (q : Point)
    (hq : q ∈ LineBundle.baseSet f ∩ LineBundle.baseSet g) :
    exceptionalCoefficient g q = LineBundle.gain 1 (-1) f g q * exceptionalCoefficient f q := by
  have hp := plane_normalization_scale (planeIndex f.1 f.2) (planeIndex g.1 g.2) (blowdown q)
    (planeChart_of_affineChart _ _ q hq.1) (planeChart_of_affineChart _ _ q hq.2)
  have hf := ((mem_affineChart_source _ _ q).mp hq.1).1
  have hg := ((mem_affineChart_source _ _ q).mp hq.2).1
  have hd := direction_normalization_scale f.1 g.1 (ruling q) hf hg
  have h := congrArg centrePair hp
  rw [map_smul,exceptionalCoefficient_incidence f q hq.1,
    exceptionalCoefficient_incidence g q hq.2,← hd] at h
  have he : ProjectivePlaneBundle.ratio (planeIndex f.1 f.2) (planeIndex g.1 g.2) (blowdown q) *
      exceptionalCoefficient f q = exceptionalCoefficient g q * ProjectiveLineBundle.ratio f.1 g.1 (ruling q) := by
    simpa only [Pi.smul_apply,smul_eq_mul,directionVector_self,mul_one] using congrFun h f.1
  have hn := ProjectiveLineBundle.ratio_ne_zero f.1 g.1 (ruling q) hf hg
  simp only [LineBundle.gain,ProjectivePlaneBundle.gain,ProjectiveLineBundle.gain,zpow_one,zpow_neg_one]
  calc
    _ = (ProjectivePlaneBundle.ratio (planeIndex f.1 f.2) (planeIndex g.1 g.2) (blowdown q) *
        exceptionalCoefficient f q) / ProjectiveLineBundle.ratio f.1 g.1 (ruling q) :=
      (eq_div_iff hn).mpr he.symm
    _ = _ := by ring

theorem centrePair_zero_iff (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    centrePair v = 0 ↔ Projectivization.mk ℂ v hv = centre := by
  constructor
  · intro h
    have h1 : v 1 = 0 := congrFun h 0
    have h2 : v 2 = 0 := congrFun h 1
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨v 0,?_⟩
    ext j
    fin_cases j <;> simp [ProjectivePlane.vector,h1,h2]
  · intro h
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    ext j
    fin_cases j
    · simpa [centre,ProjectivePlane.param,ProjectivePlane.vector,centrePair] using (congrFun ha 1).symm
    · simpa [centre,ProjectivePlane.param,ProjectivePlane.vector,centrePair] using (congrFun ha 2).symm

/-- Its zero locus is exactly the exceptional curve, including at all overlaps. -/
theorem exceptionalCoefficient_zero_iff (f : Frame) (q : Point) (hq : q ∈ LineBundle.baseSet f) :
    exceptionalCoefficient f q = 0 ↔ q ∈ exceptionalSet := by
  have he := exceptionalCoefficient_incidence f q hq
  have hp := planeChart_of_affineChart f.1 f.2 q hq
  have hc := centrePair_zero_iff
    (ProjectivePlane.vector (planeIndex f.1 f.2) (ProjectivePlane.coordinates (planeIndex f.1 f.2) (blowdown q)))
    (ProjectivePlane.vector_nonzero _ _)
  change (_ = 0 ↔ ProjectivePlane.param _ _ = centre) at hc
  rw [ProjectivePlane.param_coordinates _ _ hp] at hc
  constructor
  · intro hz
    apply hc.mp
    rw [he,hz,zero_smul]
  · intro hz
    have hh := hc.mpr hz
    rw [he] at hh
    simpa only [Pi.smul_apply,smul_eq_mul,directionVector_self,mul_one,Pi.zero_apply] using congrFun hh f.1

/-- The defining coefficient is a single coordinate on the charts meeting E. -/
theorem exceptionalCoefficient_affine_zero (i : Fin 2) (q : Coord) :
    exceptionalCoefficient (i,0) (affineParam i 0 q) = q.1 := by
  unfold exceptionalCoefficient
  change ProjectivePlane.vector _ (ProjectivePlane.coordinates _
    (fiberPlane i q.2 (ProjectiveLine.param 0 q.1))) _ = _
  rw [fiberPlane_param_planeParam i 0 q,ProjectivePlane.coordinates_param]
  fin_cases i <;> simp [planeIndex,affinePlaneCoordinates,ProjectivePlane.vector]

/-- The other two charts do not meet E; the defining section is a unit there. -/
theorem exceptionalCoefficient_affine_one (i : Fin 2) (q : Coord) :
    exceptionalCoefficient (i,1) (affineParam i 1 q) = 1 := by
  unfold exceptionalCoefficient
  change ProjectivePlane.vector _ (ProjectivePlane.coordinates _
    (fiberPlane i q.2 (ProjectiveLine.param 1 q.1))) _ = _
  rw [fiberPlane_param_planeParam i 1 q,ProjectivePlane.coordinates_param]
  fin_cases i <;> simp [planeIndex,affinePlaneCoordinates,ProjectivePlane.vector]

/-- Consequently H+E has exactly bidegree `(2,-1)` in genuine frame transitions. -/
theorem hyperplane_times_exceptional_gain (f g : Frame) (q : Point) :
    LineBundle.gain 1 0 f g q * LineBundle.gain 1 (-1) f g q = LineBundle.gain 2 (-1) f g q := by
  simp [LineBundle.gain,ProjectivePlaneBundle.gain,ProjectiveLineBundle.gain,pow_two]
  ring
  exact mul_comm _ _

end
end FailureOfSemipositiveMetricExtension.Hisamoto
