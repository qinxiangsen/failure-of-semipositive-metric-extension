import FailureOfSemipositiveMetricExtension.CentralCurveEmbedding

/-! Exact restriction cocycles along the genuine central rational curve.
The ambient (a;b₀,b₁,b₂,b₃) bundle restricts, in two explicitly verified
frames, to the existing projective-line O(a+b₃) cocycle.  This identifies
actual analytic transition data, without assuming a degree/intersection theorem. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

/-- Two ambient frames covering the actual line: the first three directions use
[1:0], while the base and the fourth direction use the same affine index. -/
def restrictionFrame (i : Fin 2) : Index := (i.castSucc,fun r => if r = 3 then i else 0)

theorem lineBase_mem_chart_iff (i : Fin 2) (d : Direction) :
    lineBase d ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet i.castSucc ↔
      d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i := by
  obtain ⟨j,s,rfl⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover d
  rw [lineBase_param,FailureOfSemipositiveMetricExtension.ProjectivePlane.param_mem_chartSet_iff,
    FailureOfSemipositiveMetricExtension.ProjectiveLine.param_mem_chartSet_iff]
  fin_cases i <;> fin_cases j <;>
    simp [FailureOfSemipositiveMetricExtension.ProjectivePlane.overlap,FailureOfSemipositiveMetricExtension.ProjectivePlane.vector,
      FailureOfSemipositiveMetricExtension.ProjectiveLine.overlap]

/-- The two chosen ambient frame domains pull back to the full standard P¹ charts. -/
theorem restrictionFrame_baseSet (i : Fin 2) :
    lineParam ⁻¹' baseSet 0 (restrictionFrame i) = FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i := by
  ext d
  change (lineBase d ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet i.castSucc ∧
    ∀ r, lineDirections d r ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet (if r = 3 then i else 0)) ↔ _
  rw [lineBase_mem_chart_iff]
  constructor
  · exact And.left
  · intro hd
    refine ⟨hd,?_⟩
    intro r
    by_cases hr : r = 3
    · simpa [lineDirections,hr] using hd
    · simp only [lineDirections,if_neg hr]
      exact ⟨0,rfl⟩

theorem restriction_plane_ratio (i j : Fin 2) (d : Direction)
    (hd : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet j) :
    FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio i.castSucc j.castSucc (lineBase d) =
      FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio i j d := by
  obtain ⟨s,rfl⟩ := hd
  rw [lineBase_param]
  fin_cases i <;> fin_cases j <;>
    simp [FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio,FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio,
      FailureOfSemipositiveMetricExtension.ProjectivePlane.vector,FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_param,
      FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates_param]
  · exact (FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates_param 1 s).symm
  · exact (FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates_param 0 s).symm

/-- The actual pulled-back ambient transition is precisely O(a+b₃). -/
theorem restriction_gain (a : ℤ) (b : Fin 4 → ℤ) (i j : Fin 2) (d : Direction)
    (hd : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i ∩ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet j) :
    gain 0 a b (restrictionFrame i) (restrictionFrame j) (lineParam d) =
      FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain (a+b 3) i j d := by
  change FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain a i.castSucc j.castSucc (lineBase d) *
    (∏ r,FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain (b r)
      (if r = 3 then i else 0) (if r = 3 then j else 0) (lineDirections d r)) = _
  rw [Fin.prod_univ_four]
  simp only [lineDirections,if_neg (show (0 : Fin 4) ≠ 3 by decide),
    if_neg (show (1 : Fin 4) ≠ 3 by decide),if_neg (show (2 : Fin 4) ≠ 3 by decide),if_pos rfl]
  simp only [FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain,FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio_self,
    one_zpow,one_mul,mul_one,FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain]
  rw [restriction_plane_ratio i j d hd.2]
  exact (zpow_add₀ (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio_ne_zero i j d hd.1 hd.2) a (b 3)).symm

theorem restriction_gain_contMDiffOn (a : ℤ) (b : Fin 4 → ℤ) (i j : Fin 2)
    (n : WithTop ℕ∞) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n
      (fun d => gain 0 a b (restrictionFrame i) (restrictionFrame j) (lineParam d))
      (FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i ∩ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet j) :=
  (gain_contMDiffOn 0 a b (restrictionFrame i) (restrictionFrame j) n).comp
    (lineParam_contMDiff n).contMDiffOn (fun d hd =>
      ⟨(Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd.1,
       (Set.ext_iff.mp (restrictionFrame_baseSet j) d).mpr hd.2⟩)

/-- A genuine analytic line-bundle core on P¹, constructed from the restricted
ambient frames rather than merely relabelling O(a+b₃). -/
def restrictedCore (a : ℤ) (b : Fin 4 → ℤ) : VectorBundleCore ℂ Direction ℂ (Fin 2) where
  baseSet := FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet
  isOpen_baseSet := FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen
  indexAt := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).indexAt
  mem_baseSet_at := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).mem_baseSet_at
  coordChange i j d := gain 0 a b (restrictionFrame i) (restrictionFrame j) (lineParam d) • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i d _ v := by simp [gain_self]
  continuousOn_coordChange i j := (restriction_gain_contMDiffOn a b i j 0).continuousOn.smul continuousOn_const
  coordChange_comp i j k d hd v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [restriction_gain a b j k d ⟨hd.1.2,hd.2⟩,
      restriction_gain a b i j d hd.1,restriction_gain a b i k d ⟨hd.1.1,hd.2⟩,
      ← mul_assoc,FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain_comp (a+b 3) i j k d hd]

instance restrictedCore_isContMDiff (a : ℤ) (b : Fin 4 → ℤ) (n : WithTop ℕ∞) :
    (restrictedCore a b).IsContMDiff 𝓘(ℂ) n where
  contMDiffOn_coordChange i j := (restriction_gain_contMDiffOn a b i j n).smul contMDiffOn_const

theorem restrictedCore_finrank (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    Module.finrank ℂ ((restrictedCore a b).Fiber d) = 1 := Module.finrank_self ℂ

theorem restrictedCore_analytic (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiffVectorBundle ω ℂ (restrictedCore a b).Fiber 𝓘(ℂ) := inferInstance

/-- Exact equality of the genuine coordinate-change linear maps on every overlap. -/
theorem restrictedCore_eq_projectiveLine_cocycle (a : ℤ) (b : Fin 4 → ℤ) (i j : Fin 2)
    (d : Direction) (hd : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i ∩ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet j) :
    (restrictedCore a b).coordChange i j d =
      (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).coordChange i j d := by
  change gain 0 a b (restrictionFrame i) (restrictionFrame j) (lineParam d) • _ = _
  rw [restriction_gain a b i j d hd]
  rfl

/-- The ℓ-divisor bundle restricts to the explicit O(-2) transition cocycle. -/
theorem ell_restriction_cocycle (i j : Fin 2) (d : Direction)
    (hd : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i ∩ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet j) :
    gain 0 (-2) ellDegree (restrictionFrame i) (restrictionFrame j) (lineParam d) =
      FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain (-2) i j d := by
  simpa [ellDegree,ellMultiplicity] using restriction_gain (-2) ellDegree i j d hd

/-- The L-type bundle restricts to the explicit O(-1) transition cocycle. -/
theorem l_restriction_cocycle (i j : Fin 2) (d : Direction)
    (hd : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i ∩ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet j) :
    gain 0 (-2) (fun _ => 1) (restrictionFrame i) (restrictionFrame j) (lineParam d) =
      FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain (-1) i j d := by
  simpa using restriction_gain (-2) (fun _ => 1) i j d hd

/-- The A-type bundle restricts to the explicit O(0) transition cocycle. -/
theorem a_restriction_cocycle (i j : Fin 2) (d : Direction)
    (hd : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i ∩ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet j) :
    gain 0 (-2) centralADegree (restrictionFrame i) (restrictionFrame j) (lineParam d) = 1 := by
  have h := restriction_gain (-2) centralADegree i j d hd
  simpa [centralADegree,centralMultiplicity,FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain] using h

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
