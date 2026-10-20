import FailureOfSemipositiveMetricExtension.GlobalCharts
import FailureOfSemipositiveMetricExtension.GlobalTopology
import FailureOfSemipositiveMetricExtension.ProjectiveLineMaps

/-!
The eight global set charts are upgraded to partial homeomorphisms for the actual
incidence-subspace topology. Continuity of the other three projective directions
uses nonzero polynomial vectors, never continuity of a chosen representative.
-/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section

open Set

/-- The projective base coordinate is continuous in the actual total-space topology. -/
theorem blowdown_continuous : Continuous blowdown := by
  exact continuous_fst.comp continuous_subtype_val

theorem direction_continuous (j : Fin 4) : Continuous (fun p : Total => directions p j) := by
  exact (continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))

theorem centre_continuous (j : Fin 4) : Continuous (centre j) := by
  simpa only [centre_eq_projectivePlane_centre] using ProjectivePlane.centre_continuous j

theorem localParam_continuous (e : Fin 2) : Continuous (localParam e) := by
  fin_cases e
  · exact Blowup.X_continuous
  · exact Blowup.Y_continuous

theorem baseCoordinates_continuous (i : Fin 4) :
    Continuous (fun q : ℂ × Blowup.Plane => baseCoordinates i q.1 q.2) := by
  fin_cases i <;> dsimp [baseCoordinates] <;> fun_prop

theorem affineBase_continuous (i : Fin 4) :
    Continuous (fun q : ℂ × Blowup.Plane => affineBase i q.1 q.2) := by
  simp_rw [affineBase_eq_param]
  exact (ProjectivePlane.param_continuous (baseChart i)).comp (baseCoordinates_continuous i)

/-- The underlying affine base of each global chart is a continuous polynomial-parametrized point. -/
theorem chartBase_continuous (i : Fin 4) (e : Fin 2) :
    Continuous (fun q : ChartCoord => affineBase i q.2 (Blowup.projection (localParam e q.1))) :=
  (affineBase_continuous i).comp
    (continuous_snd.prodMk (Blowup.projection_continuous.comp
      ((localParam_continuous e).comp continuous_fst)))

theorem chartDomain_isOpen (i : Fin 4) (e : Fin 2) : IsOpen (chartDomain i e) := by
  unfold chartDomain
  rw [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · have heq : {q : ChartCoord | j ≠ i → affineBase i q.2 (Blowup.projection (localParam e q.1)) ≠ centre j q.2} =
        {q : ChartCoord | affineBase i q.2 (Blowup.projection (localParam e q.1)) ≠ centre j q.2} := by
      ext q
      exact ⟨fun h => h hj,fun h _ => h⟩
    rw [heq]
    exact isOpen_ne_fun (chartBase_continuous i e) ((centre_continuous j).comp continuous_snd)

theorem chartSource_isOpen (i : Fin 4) (e : Fin 2) : IsOpen (chartSource i e) := by
  have haway : IsOpen {p : Total | ∀ j, j ≠ i → blowdown p ≠ centre j (projection p)} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    by_cases hj : j = i
    · subst j
      simp
    · have heq : {p : Total | j ≠ i → blowdown p ≠ centre j (projection p)} =
          {p : Total | blowdown p ≠ centre j (projection p)} := by
        ext p
        exact ⟨fun h => h hj,fun h _ => h⟩
      rw [heq]
      exact isOpen_ne_fun blowdown_continuous ((centre_continuous j).comp projection_continuous)
  have heq : chartSource i e =
      blowdown ⁻¹' ProjectivePlane.chartSet (baseChart i) ∩
      ((fun p => directions p i) ⁻¹' ProjectiveLine.chartSet e ∩
      {p : Total | ∀ j, j ≠ i → blowdown p ≠ centre j (projection p)}) := by
    ext p
    exact mem_chartSource_iff i e p
  rw [heq]
  exact ((ProjectivePlane.chartSet_isOpen _).preimage blowdown_continuous).inter
    (((ProjectiveLine.chartSet_isOpen e).preimage (direction_continuous i)).inter haway)

/-- Nonzero linear-pair vectors characterize avoidance of a centre in normalized base coordinates. -/
theorem pairMap_baseVector_ne_zero (i j : Fin 4) (t : ℂ) (w : Blowup.Plane)
    (haway : affineBase i t w ≠ centre j t) : pairMap j t (baseVector i t w) ≠ 0 := by
  intro hz
  apply haway
  exact (projective_eq_iff_mem (baseVector i t w) (baseVector_ne_zero i t w) (centre j t)).mpr
    ((pairMap_zero_iff_mem_centre j t _).mp hz)

/-- On the legitimate chart domain, the representative-defined auxiliary direction equals
an explicitly normalized polynomial-vector direction. -/
theorem chosenDirection_affineBase_eq_vectorPoint (i j : Fin 4) (t : ℂ) (w : Blowup.Plane)
    (haway : affineBase i t w ≠ centre j t) :
    chosenDirection (affineBase i t w) j t = ProjectiveLine.vectorPoint (pairMap j t (baseVector i t w)) := by
  have hv := pairMap_baseVector_ne_zero i j t w haway
  rw [ProjectiveLine.vectorPoint_eq_mk _ hv]
  symm
  apply (projective_eq_iff_mem _ hv _).mpr
  exact (incidence_mk_iff (baseVector i t w) (baseVector_ne_zero i t w) _ j t).mp
    (chosenDirection_incidence (affineBase i t w) j t)

/-- Polynomial vectors producing all auxiliary projective directions. -/
def chartPair (i : Fin 4) (e : Fin 2) (j : Fin 4) (q : ChartCoord) : Blowup.Plane :=
  pairMap j q.2 (baseVector i q.2 (Blowup.projection (localParam e q.1)))

theorem chartPair_continuous (i : Fin 4) (e : Fin 2) (j : Fin 4) :
    Continuous (chartPair i e j) := by
  have hv : Continuous (fun q : ℂ × Blowup.Plane => baseVector i q.1 q.2) := by
    apply continuous_pi
    intro k
    fin_cases i <;> fin_cases k <;> dsimp [baseVector] <;> fun_prop
  have hp : Continuous (fun q : ℂ × (Fin 3 → ℂ) => pairMap j q.1 q.2) := by
    apply continuous_pi
    intro k
    fin_cases j <;> fin_cases k <;> dsimp [pairMap,pair] <;> fun_prop
  exact hp.comp (continuous_snd.prodMk (hv.comp
    (continuous_snd.prodMk (Blowup.projection_continuous.comp
      ((localParam_continuous e).comp continuous_fst)))))

theorem chartPair_ne_zero (i : Fin 4) (e : Fin 2) (j : Fin 4) (q : ChartCoord)
    (hq : q ∈ chartDomain i e) (hj : j ≠ i) : chartPair i e j q ≠ 0 :=
  pairMap_baseVector_ne_zero i j q.2 _ (hq j hj)

/-- Continuity of all four direction coordinates on each legitimate global chart domain. -/
theorem chartParam_direction_continuousOn (i : Fin 4) (e : Fin 2) (j : Fin 4) :
    ContinuousOn (fun q => directions (chartParam i e q) j) (chartDomain i e) := by
  by_cases hj : j = i
  · subst j
    simp only [chartParam,localLift_direction,localParam_direction]
    exact ((ProjectiveLine.param_continuous e).comp (continuous_snd.comp continuous_fst)).continuousOn
  · have hc := ProjectiveLine.vectorPoint_comp_continuousOn
      (chartPair_continuous i e j).continuousOn (fun q hq => chartPair_ne_zero i e j q hq hj)
    apply hc.congr
    intro q hq
    change (if j = i then _ else _) = _
    simp only [hj,ite_false]
    exact chosenDirection_affineBase_eq_vectorPoint i j q.2 _ (hq j hj)

/-- Actual continuity into the ambient-subspace total space. -/
theorem chartParam_continuousOn (i : Fin 4) (e : Fin 2) :
    ContinuousOn (chartParam i e) (chartDomain i e) := by
  have hd : ContinuousOn (fun q => directions (chartParam i e q)) (chartDomain i e) :=
    continuousOn_pi.mpr (fun j => chartParam_direction_continuousOn i e j)
  have ha : ContinuousOn (fun q => (chartParam i e q).val) (chartDomain i e) :=
    (chartBase_continuous i e).continuousOn.prodMk (hd.prodMk continuous_snd.continuousOn)
  rw [continuousOn_iff_continuous_restrict]
  exact ha.restrict.subtype_mk (fun q => (chartParam i e q.val).property)

/-- The local pair read in the relevant normalized projective base chart. -/
def basePair (i : Fin 4) (p : Total) : Blowup.Plane := localPair (baseChart i) i p.val

def radialCoordinate (e : Fin 2) (w : Blowup.Plane) : ℂ := if e = 0 then w 0 else w 1

/-- Explicit inverse coordinates on the intrinsic chart source. -/
def explicitCoordinates (i : Fin 4) (e : Fin 2) (p : Total) : ChartCoord :=
  ((radialCoordinate e (basePair i p),ProjectiveLine.coordinates e (directions p i)),projection p)

theorem baseVector_eq_vector (i : Fin 4) (t : ℂ) (w : Blowup.Plane) :
    ProjectivePlane.vector (baseChart i) (baseCoordinates i t w) = baseVector i t w := by
  fin_cases i <;> rfl

@[simp] theorem radialCoordinate_localParam (e : Fin 2) (q : ℂ × ℂ) :
    radialCoordinate e (Blowup.projection (localParam e q)) = q.1 := by
  fin_cases e <;> rfl

@[simp] theorem explicitCoordinates_chartParam (i : Fin 4) (e : Fin 2) (q : ChartCoord) :
    explicitCoordinates i e (chartParam i e q) = q := by
  have hbase : basePair i (chartParam i e q) = Blowup.projection (localParam e q.1) := by
    change pairMap i q.2 (ProjectivePlane.vector (baseChart i)
      (ProjectivePlane.coordinates (baseChart i)
        (affineBase i q.2 (Blowup.projection (localParam e q.1))))) = _
    rw [affineBase_eq_param,ProjectivePlane.coordinates_param,baseVector_eq_vector,pairMap_baseVector]
  simp only [explicitCoordinates,hbase,radialCoordinate_localParam]
  simp [chartParam,localLift_direction,localParam_direction]

theorem chartCoordinates_eq_explicit (i : Fin 4) (e : Fin 2) (p : Total)
    (hp : p ∈ chartSource i e) : chartCoordinates i e p = explicitCoordinates i e p := by
  rcases hp with ⟨q,_,rfl⟩
  rw [chartCoordinates_param,explicitCoordinates_chartParam]

theorem basePair_continuousOn (i : Fin 4) (e : Fin 2) :
    ContinuousOn (basePair i) (chartSource i e) :=
  (localPair_continuousOn (baseChart i) i).comp continuous_subtype_val.continuousOn
    (fun p hp => (mem_chartSource_iff i e p).mp hp |>.1)

theorem radialCoordinate_continuous (e : Fin 2) : Continuous (radialCoordinate e) := by
  fin_cases e
  · exact continuous_apply 0
  · exact continuous_apply 1

theorem explicitCoordinates_continuousOn (i : Fin 4) (e : Fin 2) :
    ContinuousOn (explicitCoordinates i e) (chartSource i e) := by
  have hrad := (radialCoordinate_continuous e).comp_continuousOn (basePair_continuousOn i e)
  have hslope : ContinuousOn (fun p : Total => ProjectiveLine.coordinates e (directions p i))
      (chartSource i e) :=
    (ProjectiveLine.homeomorphChart e).continuousOn.comp (direction_continuous i).continuousOn
      (fun p hp => (mem_chartSource_iff i e p).mp hp |>.2.1)
  exact (hrad.prodMk hslope).prodMk projection_continuous.continuousOn

theorem chartCoordinates_continuousOn (i : Fin 4) (e : Fin 2) :
    ContinuousOn (chartCoordinates i e) (chartSource i e) :=
  (explicitCoordinates_continuousOn i e).congr (chartCoordinates_eq_explicit i e)

/-- Each one of the eight set charts is a genuine partial homeomorphism for the
already constructed global incidence-subspace topology. -/
def homeomorphChart (i : Fin 4) (e : Fin 2) : PartialHomeomorph Total ChartCoord where
  toPartialEquiv := partialChart i e
  open_source := chartSource_isOpen i e
  open_target := chartDomain_isOpen i e
  continuousOn_toFun := chartCoordinates_continuousOn i e
  continuousOn_invFun := chartParam_continuousOn i e

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
