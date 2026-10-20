import FailureOfSemipositiveMetricExtension.HisamotoManifold

/-! Actual analytic line bundles of bidegree `(a,b)` on the one-point incidence
surface, with transitions pulled from `O(a)` on P² and `O(b)` on the ruling
base. The refined product charts identify their exact local transitions with
`O(a)` on the fibre; this is not an inference from a numerical degree. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Bundle
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable

abbrev Frame := Fin 2 × Fin 2

/-- Plane normalization matched to the normalized fibre coordinate. -/
def planeIndex (i j : Fin 2) : Fin 3 := if j = 0 then 0 else if i = 0 then 1 else 2

def affinePlaneCoordinates (i j : Fin 2) (q : Coord) : Coord :=
  if j = 0 then (if i = 0 then (q.1,q.1*q.2) else (q.1*q.2,q.1)) else q

theorem fiberPlane_param_planeParam (i j : Fin 2) (q : Coord) :
    fiberPlane i q.2 (ProjectiveLine.param j q.1) =
      ProjectivePlane.param (planeIndex i j) (affinePlaneCoordinates i j q) := by
  rw [← directionVector_mk j q.1,fiberPlane,Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨1,?_⟩
  fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    simp [planeIndex,affinePlaneCoordinates,fiberLinear,directionVector,
      Blowup.vectorX,Blowup.vectorY,ProjectivePlane.vector]

theorem line_mk_mem_chartSet_iff (j : Fin 2) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ ProjectiveLine.chartSet j ↔ v j ≠ 0 := by
  constructor
  · rintro ⟨s,hs⟩ hj
    rw [← directionVector_mk j s] at hs
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hs
    have h := congrFun ha j
    simp [hj] at h
  · intro hj
    fin_cases j
    · exact ⟨v 1 / v 0,by
        change ProjectiveLine.param 0 (v 1 / v 0) = _
        rw [← ProjectiveLine.vectorPoint_eq_param_zero v hj,
          ProjectiveLine.vectorPoint_eq_mk v hv]⟩
    · exact ⟨v 0 / v 1,by
        change ProjectiveLine.param 1 (v 0 / v 1) = _
        rw [← ProjectiveLine.vectorPoint_eq_param_one v hj,
          ProjectiveLine.vectorPoint_eq_mk v hv]⟩

theorem fiberPlane_mem_planeChart_iff (i j : Fin 2) (t : ℂ) (p : Direction) :
    fiberPlane i t p ∈ ProjectivePlane.chartSet (planeIndex i j) ↔ p ∈ ProjectiveLine.chartSet j := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [fiberPlane,Projectivization.map_mk,ProjectivePlane.mk_mem_chartSet_iff,
      line_mk_mem_chartSet_iff]
    fin_cases i <;> fin_cases j <;>
      simp [fiberLinear,directionVector,planeIndex,Blowup.vectorX,Blowup.vectorY]

theorem planeChart_of_affineChart (i j : Fin 2) (q : Point)
    (hq : q ∈ (affineChart i j).source) : blowdown q ∈ ProjectivePlane.chartSet (planeIndex i j) := by
  have hm := (mem_affineChart_source i j q).mp hq
  rw [← localParam_localCoordinates i q hm.1,blowdown_localParam,fiberPlane_mem_planeChart_iff]
  exact hm.2

theorem localParam_mem_affineChart_iff (i j : Fin 2) (q : Direction × ℂ) :
    localParam i q ∈ (affineChart i j).source ↔ q.1 ∈ ProjectiveLine.chartSet j := by
  rw [mem_affineChart_source]
  simp only [blowdown_localParam,fiberDirection_fiberPlane]
  constructor
  · exact And.right
  · intro h
    exact ⟨by rw [rulingChart_eq_range]; exact ⟨q,rfl⟩,h⟩

/-- Exact equality of homogeneous normalization ratios over a ruling product. -/
theorem planeRatio_local (i j k : Fin 2) (t : ℂ) (p : Direction)
    (hk : p ∈ ProjectiveLine.chartSet k) :
    ProjectivePlaneBundle.ratio (planeIndex i j) (planeIndex i k) (fiberPlane i t p) =
      ProjectiveLineBundle.ratio j k p := by
  obtain ⟨s,rfl⟩ := hk
  rw [fiberPlane_param_planeParam i k (s,t)]
  unfold ProjectivePlaneBundle.ratio
  rw [ProjectivePlane.coordinates_param]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [planeIndex,affinePlaneCoordinates,ProjectivePlane.vector,
      ProjectiveLineBundle.ratio,ProjectiveLine.coordinates_param]
  all_goals first | exact (ProjectiveLine.coordinates_param 0 s).symm |
    exact (ProjectiveLine.coordinates_param 1 s).symm

namespace LineBundle

def baseSet (f : Frame) : Set Point := (affineChart f.1 f.2).source

def gain (a b : ℤ) (f g : Frame) (q : Point) : ℂ :=
  ProjectivePlaneBundle.gain a (planeIndex f.1 f.2) (planeIndex g.1 g.2) (blowdown q) *
    ProjectiveLineBundle.gain b f.1 g.1 (ruling q)

theorem gain_self (a b : ℤ) (f : Frame) (q : Point) : gain a b f f q = 1 := by
  simp [gain,ProjectivePlaneBundle.gain,ProjectivePlaneBundle.ratio_self,
    ProjectiveLineBundle.gain,ProjectiveLineBundle.ratio_self]

theorem gain_comp (a b : ℤ) (f g h : Frame) (q : Point)
    (hq : q ∈ baseSet f ∩ baseSet g ∩ baseSet h) :
    gain a b g h q * gain a b f g q = gain a b f h q := by
  have hp : blowdown q ∈ ProjectivePlane.chartSet (planeIndex f.1 f.2) ∩
      ProjectivePlane.chartSet (planeIndex g.1 g.2) ∩ ProjectivePlane.chartSet (planeIndex h.1 h.2) :=
    ⟨⟨planeChart_of_affineChart _ _ q hq.1.1,planeChart_of_affineChart _ _ q hq.1.2⟩,
      planeChart_of_affineChart _ _ q hq.2⟩
  have hr : ruling q ∈ ProjectiveLine.chartSet f.1 ∩ ProjectiveLine.chartSet g.1 ∩
      ProjectiveLine.chartSet h.1 :=
    ⟨⟨((mem_affineChart_source _ _ q).mp hq.1.1).1,
      ((mem_affineChart_source _ _ q).mp hq.1.2).1⟩,((mem_affineChart_source _ _ q).mp hq.2).1⟩
  unfold gain
  calc
    _ = (ProjectivePlaneBundle.gain a (planeIndex g.1 g.2) (planeIndex h.1 h.2) (blowdown q) *
      ProjectivePlaneBundle.gain a (planeIndex f.1 f.2) (planeIndex g.1 g.2) (blowdown q)) *
      (ProjectiveLineBundle.gain b g.1 h.1 (ruling q) * ProjectiveLineBundle.gain b f.1 g.1 (ruling q)) := by ring
    _ = _ := by rw [ProjectivePlaneBundle.gain_comp _ _ _ _ _ hp,
      ProjectiveLineBundle.gain_comp _ _ _ _ _ hr]

theorem gain_contMDiffOn (a b : ℤ) (f g : Frame) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ) n (gain a b f g) (baseSet f ∩ baseSet g) := by
  have hp : MapsTo blowdown (baseSet f ∩ baseSet g)
      (ProjectivePlane.chartSet (planeIndex f.1 f.2) ∩ ProjectivePlane.chartSet (planeIndex g.1 g.2)) :=
    fun q hq => ⟨planeChart_of_affineChart _ _ q hq.1,planeChart_of_affineChart _ _ q hq.2⟩
  have hr : MapsTo ruling (baseSet f ∩ baseSet g)
      (ProjectiveLine.chartSet f.1 ∩ ProjectiveLine.chartSet g.1) :=
    fun q hq => ⟨((mem_affineChart_source _ _ q).mp hq.1).1,((mem_affineChart_source _ _ q).mp hq.2).1⟩
  exact ((ProjectivePlaneBundle.gain_contMDiffOn a _ _ n).comp (blowdown_contMDiff n).contMDiffOn hp).smul
    ((ProjectiveLineBundle.gain_contMDiffOn b _ _ n).comp (ruling_contMDiff n).contMDiffOn hr)

/-- Actual analytic bundle obtained from the plane/base homogeneous cocycles. -/
def core (a b : ℤ) : VectorBundleCore ℂ Point ℂ Frame where
  baseSet := baseSet
  isOpen_baseSet f := (affineChart f.1 f.2).open_source
  indexAt q := Classical.choose (affineCharts_cover q)
  mem_baseSet_at q := Classical.choose_spec (affineCharts_cover q)
  coordChange f g q := gain a b f g q • ContinuousLinearMap.id ℂ ℂ
  coordChange_self f q _ v := by simp [gain_self]
  continuousOn_coordChange f g := (gain_contMDiffOn a b f g 0).continuousOn.smul continuousOn_const
  coordChange_comp f g h q hq v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc,gain_comp a b f g h q hq]

instance core_isContMDiff (a b : ℤ) (n : WithTop ℕ∞) : (core a b).IsContMDiff 𝓘(ℂ,Coord) n where
  contMDiffOn_coordChange f g := (gain_contMDiffOn a b f g n).smul contMDiffOn_const

theorem actual_analytic_lineBundle (a b : ℤ) : ContMDiffVectorBundle ω ℂ (core a b).Fiber 𝓘(ℂ,Coord) :=
  inferInstance

/-- On a fixed ruling chart the base factor is trivial and the plane factor is
exactly the fibre O(a) cocycle, for every positive or negative base degree. -/
theorem gain_local (a b : ℤ) (i j k : Fin 2) (q : Direction × ℂ)
    (hk : q.1 ∈ ProjectiveLine.chartSet k) :
    gain a b (i,j) (i,k) (localParam i q) = ProjectiveLineBundle.gain a j k q.1 := by
  simp only [gain,blowdown_localParam,ruling_localParam,ProjectivePlaneBundle.gain,
    ProjectiveLineBundle.gain,ProjectiveLineBundle.ratio_self,one_zpow,mul_one]
  rw [planeRatio_local i j k q.2 q.1 hk]

/-- The Hisamoto bidegree `(2,-1)` has the actual O(2) transition functions. -/
theorem hisamoto_gain_local (i j k : Fin 2) (q : Direction × ℂ)
    (hk : q.1 ∈ ProjectiveLine.chartSet k) :
    gain 2 (-1) (i,j) (i,k) (localParam i q) = ProjectiveLineBundle.gain 2 j k q.1 :=
  gain_local 2 (-1) i j k q hk

end LineBundle
end
end FailureOfSemipositiveMetricExtension.Hisamoto
