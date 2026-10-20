import FailureOfSemipositiveMetricExtension.GlobalBundleSections

/-! The four actual analytic exceptional-divisor sections. Their vanishing loci
are proved to be precisely the four inverse images of the centre graphs. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable

def exceptionalDegree (r : Fin 4) : Fin 4 → ℤ := fun j => if j = r then -1 else 0

theorem gain_exceptional (r : Fin 4) (i j : Index) (p : Total) :
    gain 1 (exceptionalDegree r) i j p =
      FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio i.1 j.1 (blowdown p) *
        (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio (i.2 r) (j.2 r) (directions p r))⁻¹ := by
  simp [gain,exceptionalDegree,FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain,
    FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain]

theorem normalizedVector_change (i j : Fin 3) (p : FailureOfSemipositiveMetricExtension.ProjectivePlane.Point)
    (hi : p ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet i)
    (hj : p ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet j) :
    FailureOfSemipositiveMetricExtension.ProjectivePlane.vector j (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates j p) =
      FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio i j p •
        FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i p) := by
  have ht := FailureOfSemipositiveMetricExtension.ProjectivePlane.vector_transition j i
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates j p)
    (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.coordinates_mem_overlap i j p hi hj)
  have hc : FailureOfSemipositiveMetricExtension.ProjectivePlane.transition j i
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates j p) = FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i p := by
    rw [← FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_transition j i
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates j p)
      (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.coordinates_mem_overlap i j p hi hj),
      FailureOfSemipositiveMetricExtension.ProjectivePlane.param_coordinates j p hj]
  rw [hc] at ht
  exact ht.symm

theorem direction_component_change (e f : Fin 2) (d : FailureOfSemipositiveMetricExtension.ProjectiveLine.Point)
    (he : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet e)
    (hf : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet f)
    (w : Fin 2 → ℂ) (hw : w ∈ d.submodule) :
    w f = (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio e f d)⁻¹ * w e := by
  fin_cases e <;> fin_cases f
  · simp [FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio]
  · have hz := FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio_ne_zero 0 1 d he hf
    simp [FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio] at hz ⊢
    have hm : w 0 = w 1 * FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates 1 d := by
      apply (FailureOfSemipositiveMetricExtension.ProjectiveIncidence.mem_lineY_iff _ _).mp
      simpa only [← FailureOfSemipositiveMetricExtension.ProjectiveLine.param_one,
        FailureOfSemipositiveMetricExtension.ProjectiveLine.param_coordinates 1 d hf] using hw
    rw [hm]
    field_simp
  · have hz := FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio_ne_zero 1 0 d he hf
    simp [FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio] at hz ⊢
    have hm : w 1 = w 0 * FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates 0 d := by
      apply (FailureOfSemipositiveMetricExtension.ProjectiveIncidence.mem_lineX_iff _ _).mp
      simpa only [← FailureOfSemipositiveMetricExtension.ProjectiveLine.param_zero,
        FailureOfSemipositiveMetricExtension.ProjectiveLine.param_coordinates 0 d hf] using hw
    rw [hm]
    field_simp
  · simp [FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio]

theorem direction_component_zero_iff (e : Fin 2) (d : FailureOfSemipositiveMetricExtension.ProjectiveLine.Point)
    (he : d ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet e)
    (w : Fin 2 → ℂ) (hw : w ∈ d.submodule) : w e = 0 ↔ w = 0 := by
  constructor
  · intro hz
    fin_cases e
    · have hm : w 1 = w 0 * FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates 0 d := by
        apply (FailureOfSemipositiveMetricExtension.ProjectiveIncidence.mem_lineX_iff _ _).mp
        simpa only [← FailureOfSemipositiveMetricExtension.ProjectiveLine.param_zero,
          FailureOfSemipositiveMetricExtension.ProjectiveLine.param_coordinates 0 d he] using hw
      ext j; fin_cases j <;> simp_all
    · have hm : w 0 = w 1 * FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates 1 d := by
        apply (FailureOfSemipositiveMetricExtension.ProjectiveIncidence.mem_lineY_iff _ _).mp
        simpa only [← FailureOfSemipositiveMetricExtension.ProjectiveLine.param_one,
          FailureOfSemipositiveMetricExtension.ProjectiveLine.param_coordinates 1 d he] using hw
      ext j; fin_cases j <;> simp_all
  · intro h; simp [h]

def exceptionalCoefficient (r : Fin 4) (i : Index) (p : Total) : ℂ :=
  pairMap r (projection p)
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (blowdown p))) (i.2 r)

theorem normalizedPair_mem (r : Fin 4) (a : Fin 3) (p : Total)
    (hp : blowdown p ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet a) :
    pairMap r (projection p) (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector a
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates a (blowdown p))) ∈ (directions p r).submodule :=
  (incidence_localPair_iff a r p.val hp).mp (p.property r)

theorem exceptionalCoefficient_transition (r : Fin 4) (i j : Index) (p : Total)
    (hp : p ∈ baseSet i ∩ baseSet j) :
    gain 1 (exceptionalDegree r) i j p * exceptionalCoefficient r i p =
      exceptionalCoefficient r j p := by
  rw [gain_exceptional]
  unfold exceptionalCoefficient
  rw [normalizedVector_change i.1 j.1 (blowdown p) hp.1.1 hp.2.1,map_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [direction_component_change (i.2 r) (j.2 r) (directions p r)
    (hp.1.2 r) (hp.2.2 r) _ (normalizedPair_mem r i.1 p hp.1.1)]
  ring


theorem exceptionalCoefficient_contMDiffOn (r : Fin 4) (i : Index) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (exceptionalCoefficient r i) (baseSet i) := by
  have hc : ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) ω
      (fun p => FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (blowdown p)) (baseSet i) :=
    (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.coordinates_contMDiffOn i.1 ω).comp
      (blowdown_contMDiff ω).contMDiffOn (fun _ hp => hp.1)
  have hv (j : Fin 3) : ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω
      (fun p => FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1
        (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (blowdown p)) j) (baseSet i) := by
    have ha : ContDiff ℂ ω (fun q : ℂ × ℂ => FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1 q j) := by
      rcases i with ⟨a,b⟩
      fin_cases a <;> fin_cases j <;> dsimp [FailureOfSemipositiveMetricExtension.ProjectivePlane.vector] <;> fun_prop
    exact ha.contMDiff.comp_contMDiffOn hc
  have ht := (projection_contMDiff ω).contMDiffOn (s := baseSet i)
  unfold exceptionalCoefficient
  generalize he : i.2 r = e
  fin_cases r <;> fin_cases e
  · exact hv 1
  · exact hv 2
  · exact hv 0
  · exact hv 2
  · have hs : ContDiff ℂ ω (fun q : ℂ × ℂ => q.1 - q.2) := by fun_prop
    exact hs.contMDiff.comp_contMDiffOn ((hv 1).prodMk_space (hv 0))
  · have hs : ContDiff ℂ ω (fun q : ℂ × ℂ => q.1 - q.2) := by fun_prop
    exact hs.contMDiff.comp_contMDiffOn ((hv 2).prodMk_space (ht.smul (hv 0)))
  · exact hv 0
  · exact hv 1

/-- The actual analytic section of multidegree (1;0,...,-1,...,0). -/
def exceptionalSection (r : Fin 4) : SectionData 1 (exceptionalDegree r) where
  coefficient := exceptionalCoefficient r
  analytic := exceptionalCoefficient_contMDiffOn r
  compatible := exceptionalCoefficient_transition r

theorem exceptionalCoefficient_zero_iff (r : Fin 4) (i : Index) (p : Total)
    (hp : p ∈ baseSet i) :
    exceptionalCoefficient r i p = 0 ↔ blowdown p = centre r (projection p) := by
  unfold exceptionalCoefficient
  rw [direction_component_zero_iff (i.2 r) (directions p r) (hp.2 r) _
    (normalizedPair_mem r i.1 p hp.1),pairMap_zero_iff_mem_centre]
  rw [← projective_eq_iff_mem _ (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector_nonzero _ _)]
  change FailureOfSemipositiveMetricExtension.ProjectivePlane.param i.1
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (blowdown p)) = _ ↔ _
  rw [FailureOfSemipositiveMetricExtension.ProjectivePlane.param_coordinates i.1 (blowdown p) hp.1]

/-- The zero vector criterion is in the actual bundle fibre, independent of all chart choices. -/
theorem exceptionalSection_zero_iff (r : Fin 4) (p : Total) :
    sectionValue (exceptionalSection r) p = 0 ↔ blowdown p = centre r (projection p) := by
  rw [sectionValue_zero_iff (exceptionalSection r)
    ((core 1 (exceptionalDegree r)).indexAt p) p
      ((core 1 (exceptionalDegree r)).mem_baseSet_at p)]
  exact exceptionalCoefficient_zero_iff r _ p ((core 1 (exceptionalDegree r)).mem_baseSet_at p)

/-- The exceptional divisor section itself, not merely its coefficients, is analytic. -/
theorem exceptionalSection_contMDiff (r : Fin 4) :
    ContMDiff 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      (sectionMap (exceptionalSection r)) := sectionMap_contMDiff _

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
